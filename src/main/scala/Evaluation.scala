import Common.*
import Common.BD.*
import Common.Icit.*
import Core.*
import Core.Tm.*
import Core.ProjType.*
import Value.*
import Value.Head.*
import Value.Val.*
import Value.Elim.*
import Value.Clos.*
import Errors.*
import Globals.*
import Metas.*
import Metas.MetaEntry.*
import Primitives.*

object Evaluation:
  def vinst(cl: Clos, v: Val): Val = cl match
    case ClosEnv(env, tm) => eval(v :: env, tm)
    case ClosFun(fn)      => fn(v)

  def force(v: Val, forceGlobals: Boolean = true): Val = v match
    case VGlobal(_, _, value) if forceGlobals => force(value(), true)
    case ne @ VNe(HMeta(id), sp) =>
      getMeta(id) match
        case Unsolved       => ne
        case Solved(sol, _) => force(sp.foldRight(sol)(velim), forceGlobals)
    case _ => v

  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, body) => vinst(body, arg)
    case VNe(hd, spine)   => VNe(hd, EApp(arg, icit) :: spine)
    case VGlobal(hd, spine, value) =>
      VGlobal(hd, EApp(arg, icit) :: spine, () => vapp(value(), arg, icit))
    case _ => throw Impossible()

  def vproj(v: Val, proj: ProjType): Val = v match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(x, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VNe(hd, spine) => VNe(hd, EProj(proj) :: spine)
    case VGlobal(hd, spine, value) =>
      VGlobal(hd, EProj(proj) :: spine, () => vproj(value(), proj))
    case _ => throw Impossible()

  def vfst(v: Val): Val = vproj(v, Fst)
  def vsnd(v: Val): Val = vproj(v, Snd)

  def velim(e: Elim, v: Val): Val = e match
    case EApp(arg, icit)   => vapp(v, arg, icit)
    case EProj(proj)       => vproj(v, proj)
    case EPrim(name, args) => vprimelim(name, v, args)

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Unsolved     => VMeta(id)
    case Solved(v, _) => v

  def vinsertedmeta(env: Env, id: MetaId, bds: BDs): Val =
    def go(env: Env, bds: BDs): Val = (env, bds) match
      case (Nil, Nil)                     => vmeta(id)
      case (v :: env, Bound(icit) :: bds) => vapp(go(env, bds), v, icit)
      case (_ :: env, Defined :: bds)     => go(env, bds)
      case _                              => throw Impossible()
    go(env, bds)

  def vprimelim(name: Name, scrut: Val, args: List[(Val, Icit)]): Val =
    (name, scrut, args) match
      case ("elimBool", VPrim("True"), List(_, (t, _), _))  => t
      case ("elimBool", VPrim("False"), List(_, _, (f, _))) => f

      case ("eqLabel", VLabelLit(x), List((VLabelLit(y), _))) =>
        if x == y then VPrimTrue else VPrimFalse

      // elimIFix {I} {F} P alg {i} (IIn {I} {F} {i} x) ~> alg (\{j} y. elimIFix {I} {F} p alg {j} y) {i} x
      case (
            "elimIFix",
            VPrimArgs("IIn", List(_, _, (i, _), (x, _))),
            List((it, _), (f, _), (p, _), (alg, _), _)
          ) =>
        vapp(
          vapp(
            vapp(
              alg,
              VLam(
                "j",
                Impl,
                ClosFun(j =>
                  VLam(
                    "y",
                    Expl,
                    ClosFun(y => vprimelim(name, y, args.init :+ (j, Impl)))
                  )
                )
              ),
              Expl
            ),
            i,
            Impl
          ),
          x,
          Expl
        )

      // elimId {A} {x} P refl {y} (Refl {_} {_} x y) ~> refl
      case ("elimId", VPrimArgs("Refl", _), List(_, _, _, (refl, _), _)) =>
        refl

      case (_, VNe(hd, spine), _) => VNe(hd, EPrim(name, args) :: spine)
      case (_, VGlobal(hd, spine, value), _) =>
        VGlobal(
          hd,
          EPrim(name, args) :: spine,
          () => vprimelim(name, value(), args)
        )
      case _ => throw Impossible()

  def eval(env: Env, tm: Tm): Val = tm match
    case Var(ix) => ixEnv(env, ix)
    case Prim(name) if isPrimitiveEliminator(name) =>
      getPrimitive(name) match
        case Some((tm, _)) => vprimelimLambda(name, tm)
        case None          => throw Impossible()
    case Prim(name) => VPrim(name)
    case Global(name) =>
      getGlobal(name) match
        case Some(ge) => ge.vglobal
        case None     => throw Impossible()
    case Let(x, _, value, body) => eval(eval(env, value) :: env, body)
    case Type                   => VType
    case LabelLit(x)            => VLabelLit(x)

    case Pi(x, icit, ty, body) =>
      VPi(x, icit, eval(env, ty), ClosEnv(env, body))
    case Lam(x, icit, body) => VLam(x, icit, ClosEnv(env, body))
    case App(fn, arg, icit) => vapp(eval(env, fn), eval(env, arg), icit)

    case Sigma(x, ty, body) => VSigma(x, eval(env, ty), ClosEnv(env, body))
    case Pair(fst, snd)     => VPair(eval(env, fst), eval(env, snd))
    case Proj(tm, proj)     => vproj(eval(env, tm), proj)

    case Meta(id)              => vmeta(id)
    case InsertedMeta(id, bds) => vinsertedmeta(env, id, bds)

  private def vprimelimLambda(
      name: Name,
      ty: Tm,
      i: Int = 0,
      args: List[(Val, Icit)] = List.empty
  ): Val = ty match
    case Pi(x, icit, _, b) =>
      val y = if x == "_" then s"$x$i" else x
      VLam(
        y,
        icit,
        ClosFun(arg => vprimelimLambda(name, b, i + 1, args :+ (arg, icit)))
      )
    case _ if args.nonEmpty && args.last._2 == Expl =>
      vprimelim(name, args.last._1, args.init)
    case _ => throw Impossible()

  private def quoteSp(lvl: Lvl, tm: Tm, sp: Spine, forceGlobals: Boolean): Tm =
    sp match
      case Nil => tm
      case EApp(arg, icit) :: sp =>
        App(
          quoteSp(lvl, tm, sp, forceGlobals),
          quote(lvl, arg, forceGlobals),
          icit
        )
      case EProj(proj) :: sp =>
        Proj(quoteSp(lvl, tm, sp, forceGlobals), proj)
      case EPrim(name, args) :: sp =>
        val scrut = quoteSp(lvl, tm, sp, forceGlobals)
        val head = args.foldLeft(Prim(name)) { case (prev, (v, icit)) =>
          App(prev, quote(lvl, v, forceGlobals), icit)
        }
        App(head, scrut, Expl)

  private def quoteHead(lvl: Lvl, head: Head): Tm = head match
    case HVar(head)  => Var(lvl2ix(lvl, head))
    case HMeta(id)   => Meta(id)
    case HPrim(name) => Prim(name)

  def quote(lvl: Lvl, value: Val, forceGlobals: Boolean = false): Tm =
    force(value, forceGlobals) match
      case VNe(head, sp) => quoteSp(lvl, quoteHead(lvl, head), sp, forceGlobals)
      case VGlobal(head, sp, _) => quoteSp(lvl, Global(head), sp, forceGlobals)
      case VType                => Type
      case VLabelLit(x)         => LabelLit(x)

      case VPi(x, icit, ty, body) =>
        Pi(
          x,
          icit,
          quote(lvl, ty, forceGlobals),
          quote(lvlInc(lvl), vinst(body, VVar(lvl)), forceGlobals)
        )
      case VLam(x, icit, body) =>
        Lam(x, icit, quote(lvlInc(lvl), vinst(body, VVar(lvl)), forceGlobals))

      case VSigma(x, ty, body) =>
        Sigma(
          x,
          quote(lvl, ty, forceGlobals),
          quote(lvlInc(lvl), vinst(body, VVar(lvl)), forceGlobals)
        )
      case VPair(fst, snd) =>
        Pair(quote(lvl, fst, forceGlobals), quote(lvl, snd, forceGlobals))

  def nf(env: Env, tm: Tm): Tm =
    quote(lvlFromEnv(env), eval(env, tm), forceGlobals = true)
