import Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.getGlobal

object Evaluation:
  extension (c: Clos)
    def inst(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(v :: env)
      case CFun(fn)       => fn(v)

  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, b)  => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg, icit))
    case VFlex(hd, sp)  => VFlex(hd, SApp(sp, arg, icit))
    case VUri(uri, sp, v) =>
      VUri(uri, SApp(sp, arg, icit), () => vapp(v(), arg, icit))
    case _ => impossible()

  def vproj(tm: Val, proj: ProjType): Val = tm match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp)   => VRigid(hd, SProj(sp, proj))
    case VFlex(hd, sp)    => VFlex(hd, SProj(sp, proj))
    case VUri(uri, sp, v) => VUri(uri, SProj(sp, proj), () => vproj(v(), proj))
    case _                => impossible()

  def vprim(x: PrimElimName, args: List[(Val, Icit)], v: Val): Val =
    (x, args, v) match
      // elimBool P t f True ~> t
      case (PElimBool, List((p, _), (t, _), (f, _)), VTrue()) => t
      // elimBool P t f False ~> f
      case (PElimBool, List((p, _), (t, _), (f, _)), VFalse()) => f
      // elimId {a} {x} P refl Refl ~> refl
      case (
            PElimId,
            List((a, _), (x, _), (p, _), (refl, _), (y, _)),
            VRefl(_, _)
          ) =>
        refl
      // elimFix {I} {F} P alg {i} (Roll {I} {F} {i} x) ~> alg (\{i} x. elimFix {I} {F} P alg {i} x) {i} x
      case (
            PElimFix,
            List((ii, _), (f, _), (p, _), (alg, _), _),
            VRoll(_, _, i, x)
          ) =>
        vapp(
          vapp(
            vapp(
              alg,
              vlamI(
                "i",
                i =>
                  vlamE(
                    "x",
                    x => vprim(PElimFix, args.init ++ List((i, Impl)), x)
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
      case (_, _, VRigid(hd, sp)) => VRigid(hd, SPrim(x, args, sp))
      case (_, _, VFlex(hd, sp))  => VFlex(hd, SPrim(x, args, sp))
      case (_, _, VUri(hd, sp, v)) =>
        VUri(hd, SPrim(x, args, sp), () => vprim(x, args, v()))
      case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId                => v
    case SApp(sp, a, i)     => vapp(vspine(v, sp), a, i)
    case SProj(sp, proj)    => vproj(vspine(v, sp), proj)
    case SPrim(x, args, sp) => vprim(x, args, vspine(v, sp))

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_, _)  => VMeta(id)

  def vcheck(id: CheckId)(implicit env: Env): Val = getCheck(id) match
    case Unchecked(ctx, t, a, m) => vappPruning(vmeta(m), ctx.pruning)
    case Checked(t)              => eval(t)

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (Nil, Nil)                => v
      case (t :: env, Some(i) :: pr) => vapp(vappPruning(v, pr)(env), t, i)
      case (_ :: env, None :: pr)    => vappPruning(v, pr)(env)
      case _                         => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Type    => VType
    case Var(ix) => env(ix)
    case Uri(uri) =>
      getGlobal(uri) match
        case None => impossible()
        case Some(e) =>
          val value = e.value
          VUri(uri, SId, () => value)
    case Prim(Right(x))  => VPrim(x)
    case Prim(Left(x))   => evalprimelim(x)
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)

    case Lam(x, i, b)   => VLam(x, i, Clos(b))
    case App(f, a, i)   => vapp(eval(f), eval(a), i)
    case Pi(x, i, t, b) => VPi(x, i, eval(t), Clos(b))

    case Pair(fst, snd) => VPair(eval(fst), eval(snd))
    case Proj(tm, proj) => vproj(eval(tm), proj)
    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))

    case Wk(tm) => eval(tm)(env.tail)

    case Meta(id)           => vmeta(id)
    case AppPruning(tm, pr) => vappPruning(eval(tm), pr)
    case PostponedCheck(c)  => vcheck(c)

  def evalprimelim(x: PrimElimName): Val = x match
    case PAbsurd =>
      vlamI("A", A => vlamE("x", x => vprim(PAbsurd, List((A, Impl)), x)))
    case PElimBool =>
      vlamE(
        "P",
        P =>
          vlamE(
            "t",
            t =>
              vlamE(
                "f",
                f =>
                  vlamE(
                    "b",
                    b =>
                      vprim(PElimBool, List((P, Expl), (t, Expl), (f, Expl)), b)
                  )
              )
          )
      )
    case PElimId =>
      vlamI(
        "A",
        A =>
          vlamI(
            "x",
            x =>
              vlamE(
                "P",
                P =>
                  vlamE(
                    "refl",
                    refl =>
                      vlamI(
                        "y",
                        y =>
                          vlamE(
                            "p",
                            p =>
                              vprim(
                                PElimId,
                                List(
                                  (A, Impl),
                                  (x, Impl),
                                  (P, Expl),
                                  (refl, Expl),
                                  (y, Impl)
                                ),
                                p
                              )
                          )
                      )
                  )
              )
          )
      )
    case PElimFix =>
      vlamI(
        "I",
        I =>
          vlamI(
            "F",
            F =>
              vlamE(
                "P",
                P =>
                  vlamE(
                    "alg",
                    alg =>
                      vlamI(
                        "i",
                        i =>
                          vlamE(
                            "x",
                            x =>
                              vprim(
                                PElimFix,
                                List(
                                  (I, Impl),
                                  (F, Impl),
                                  (P, Expl),
                                  (alg, Expl),
                                  (i, Impl)
                                ),
                                x
                              )
                          )
                      )
                  )
              )
          )
      )

  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _, _) => force(vspine(v, sp))
        case Unsolved(_, _)  => v
    case VUri(_, _, w) if unfold == UnfoldAll => force(w(), UnfoldAll)
    case _                                    => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)
      case SPrim(x, args, sp) =>
        App(
          args.foldLeft(Prim(Left(x))) { case (fn, (arg, i)) =>
            App(fn, quote(arg, unfold), i)
          },
          quote(hd, sp, unfold),
          Expl
        )

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)
    case HPrim(x) => Prim(Right(x))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VType            => Type
      case VRigid(hd, sp)   => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)    => quote(Meta(id), sp, unfold)
      case VUri(uri, sp, _) => quote(Uri(uri), sp, unfold)

      case VLam(x, i, b) => Lam(x, i, quote(b.inst(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b.inst(VVar(l)), unfold)(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b.inst(VVar(l)), unfold)(l + 1))

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)
