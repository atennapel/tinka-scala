import Common.*
import Core.*
import Value.*
import Metas.*
import Errors.*
import Globals.*
import Debug.*

object Evaluation:
  extension (c: Clos[Val])
    def apply(v: Val): Val = c match
      case CClos(env, tm) => tm.eval(Right(v) :: env)
      case CFun(fn)       => fn(v)

  extension (c: Clos[VFinLevel])
    def apply(v: VFinLevel): Val = c match
      case CClos(env, tm) => tm.eval(Left(v) :: env)
      case CFun(fn)       => fn(v)

  extension (c: ClosLvl)
    def apply(v: VFinLevel): VLevel = c.tm.eval(Left(v) :: c.env)

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_, _)  => VMeta(id)

  def vlmeta(id: LMetaId): VFinLevel = getLMeta(id) match
    case LSolved(v)      => v
    case LUnsolved(_, _) => VFinLevel.meta(id)

  private def vcheck(id: PostponeId)(implicit env: Env): Val = getCheck(
    id
  ) match
    case Unchecked(ctx, t, a, _, m) => vappPruning(vmeta(m), ctx.pruning)
    case Checked(t)                 => t.eval

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (Nil, Nil)                         => v
      case (Right(t) :: env, Some(i) :: pr)   => vappPruning(v, pr)(env)(t, i)
      case (Left(t) :: env, Some(Impl) :: pr) => vappPruning(v, pr)(env)(t)
      case (_ :: env, None :: pr)             => vappPruning(v, pr)(env)
      case _                                  => throw Impossible

  private def vliftterm(k: VFinLevel, l: VFinLevel, a: VTy, x: Val): Val =
    x match
      case VNe(hd, SPrim(sp, PLower, args)) => VNe(hd, sp)
      case VGlobal(hd, lvl, SPrim(sp, PLower, args), v) =>
        VGlobal(hd, lvl, sp, () => vliftterm(k, l, a, v()))
      case _ => VLiftTerm(k, l, a, x)

  private def vprim(x: PrimName) = x match
    case PLiftTerm =>
      vlamlvl(
        "k",
        k =>
          vlamlvl(
            "l",
            l => vlami("A", a => vlam("x", x => vliftterm(k, l, a, x)))
          )
      )
    case PLower =>
      vlamlvl(
        "k",
        k =>
          vlamlvl(
            "l",
            l =>
              vlami(
                "A",
                a =>
                  vlam(
                    "x",
                    x =>
                      x.primelim(
                        PLower,
                        List(Left(k), Left(l), Right((a, Impl)))
                      )
                  )
              )
          )
      )
    case _ => VPrim(x)

  extension (l: FinLevel)
    def eval(implicit env: Env): VFinLevel = l match
      case LVar(ix)   => ix.index(env).swap.toOption.get
      case LZ         => VFinLevel.unit
      case LS(a)      => a.eval + 1
      case LMax(a, b) => a.eval max b.eval
      case LMeta(id)  => vlmeta(id)

  extension (l: Level)
    def eval(implicit env: Env): VLevel = l match
      case LOmega       => VOmega
      case LOmega1      => VOmega1
      case LFinLevel(l) => VFL(l.eval)

  extension (c: Tm)
    def eval(implicit env: Env): Val = c match
      case Type(l)     => VType(l.eval)
      case LabelLit(x) => VLabelLit(x)
      case Var(ix)     => ix.index(env).toOption.get
      case Global(x, lvl) =>
        val value = getGlobalByLvl(lvl).get.value
        VGlobal(x, lvl, SId, () => value)
      case Prim(x)                => vprim(x)
      case Let(_, _, value, body) => body.eval(Right(value.eval) :: env)
      case App(fn, arg, icit)     => fn.eval(env)(arg.eval, icit)
      case AppLvl(fn, arg)        => fn.eval(env)(arg.eval)
      case Pi(bind, icit, ty, u1, body, u2) =>
        VPi(bind, icit, ty.eval, u1.eval, CClos(env, body), u2.eval)
      case PiLvl(x, body, u) => VPiLvl(x, CClos(env, body), ClosLvl(env, u))
      case LamLvl(x, body)   => VLamLvl(x, CClos(env, body))
      case Sigma(bind, ty, u1, body, u2) =>
        VSigma(bind, ty.eval, u1.eval, CClos(env, body), u2.eval)
      case Lam(bind, icit, body) => VLam(bind, icit, CClos(env, body))
      case Pair(fst, snd)        => VPair(fst.eval, snd.eval)
      case Proj(tm, proj)        => tm.eval.proj(proj)
      case Meta(id)              => vmeta(id)
      case AppPruning(tm, pr)    => vappPruning(tm.eval, pr)
      case PostponedCheck(c)     => vcheck(c)

    def nf: Tm = c.eval(Nil).quoteWithUnfold(lvl0, UnfoldAll)

  extension (l: VFinLevel)
    def quote(implicit k: Lvl): FinLevel =
      val fl = l.force
      val vars = fl.vars.foldLeft(LZ + fl.k) { case (i, (x, n)) =>
        i max (LVar(mkLvl(x).toIx) + n)
      }
      fl.metas.foldLeft(vars) { case (i, (x, n)) =>
        i max (LMeta(lmetaId(x)) + n)
      }

    def force: VFinLevel =
      l.metas
        .map { (id, n) =>
          getLMeta(lmetaId(id)) match
            case LUnsolved(_, _) => vlmeta(lmetaId(id)) + n
            case LSolved(v)      => (v + n).force
        }
        .foldRight(VFinLevel(l.k, l.vars))(_ max _)

  extension (l: VLevel)
    def quote(implicit k: Lvl): Level = l match
      case VOmega  => LOmega
      case VOmega1 => LOmega1
      case VFL(l)  => LFinLevel(l.quote)

    def force: VLevel = l match
      case VFL(l) => VFL(l.force)
      case _      => l

  extension (hd: Head)
    def quote(implicit k: Lvl): Tm = hd match
      case HVar(lvl) => Var(lvl.toIx)
      case HPrim(x)  => Prim(x)
      case HMeta(id) => Meta(id)

  extension (sp: Spine)
    def quoteWithUnfold(hd: Tm)(implicit k: Lvl, unfold: Unfold): Tm = sp match
      case SId => hd
      case SApp(sp, arg, icit) =>
        App(sp.quoteWithUnfold(hd), arg.quoteWithUnfold, icit)
      case SAppLvl(sp, arg) =>
        AppLvl(sp.quoteWithUnfold(hd), arg.quote)
      case SProj(sp, proj) => Proj(sp.quoteWithUnfold(hd), proj)
      case SPrim(sp, x, args) =>
        App(
          args.foldLeft(Prim(x))((fn, arg) =>
            arg.fold(
              lv => AppLvl(fn, lv.quote),
              (a, i) => App(fn, a.quoteWithUnfold, i)
            )
          ),
          sp.quoteWithUnfold(hd),
          Expl
        )

    def quote(hd: Tm)(implicit k: Lvl): Tm =
      sp.quoteWithUnfold(hd)(k, UnfoldMetas)

  extension (v: Val)
    def apply(arg: Val, icit: Icit): Val = v match
      case VLam(_, _, body) => body(arg)
      case VNe(hd, sp)      => VNe(hd, SApp(sp, arg, icit))
      case VGlobal(x, lvl, sp, v) =>
        VGlobal(x, lvl, SApp(sp, arg, icit), () => v()(arg, icit))
      case _ => throw Impossible

    def apply(arg: VFinLevel): Val = v match
      case VLamLvl(_, body) => body(arg)
      case VNe(hd, sp)      => VNe(hd, SAppLvl(sp, arg))
      case VGlobal(x, lvl, sp, v) =>
        VGlobal(x, lvl, SAppLvl(sp, arg), () => v()(arg))
      case _ => throw Impossible

    def apply(sp: Spine): Val = sp match
      case SId                => v
      case SApp(sp, a, i)     => v(sp)(a, i)
      case SAppLvl(sp, a)     => v(sp)(a)
      case SProj(sp, p)       => v(sp).proj(p)
      case SPrim(sp, x, args) => v(sp).primelim(x, args)

    def force: Val = v match
      case VNe(HMeta(m), sp) =>
        getMeta(m) match
          case Solved(v, _, _) => (v(sp)).force
          case Unsolved(_, _)  => v
      case VGlobal(_, _, _, v) => v().force
      case _                   => v

    def forceMetas: Val = v match
      case VNe(HMeta(m), sp) =>
        getMeta(m) match
          case Solved(v, _, _) => (v(sp)).forceMetas
          case Unsolved(_, _)  => v
      case _ => v

    def proj(proj: ProjType): Val = (v, proj) match
      case (VPair(fst, _), Fst)         => fst
      case (VPair(_, snd), Snd)         => snd
      case (VPair(fst, _), Named(_, 0)) => fst
      case (VPair(_, snd), Named(x, i)) => snd.proj(Named(x, i - 1))
      case (VNe(hd, sp), _)             => VNe(hd, SProj(sp, proj))
      case (VGlobal(x, lvl, sp, v), _) =>
        VGlobal(x, lvl, SProj(sp, proj), () => v().proj(proj))
      case _ => throw Impossible

    def primelim(x: PrimName, args: List[Either[VFinLevel, (Val, Icit)]]): Val =
      (v, x, args) match
        // lower <k> <l> {A} (lift <k> <l> {A} t) ~> t
        case (VLiftTerm(_, _, _, t), PLower, _) => t

        case (VNe(hd, sp), _, _) => VNe(hd, SPrim(sp, x, args))
        case (VGlobal(y, lvl, sp, v), _, _) =>
          VGlobal(y, lvl, SPrim(sp, x, args), () => v().primelim(x, args))
        case _ => throw Impossible

    def quoteWithUnfold(implicit k: Lvl, unfold: Unfold): Tm =
      val w = unfold match
        case UnfoldAll   => v.force
        case UnfoldMetas => v.forceMetas
      w match
        case VType(l)         => Type(l.quote)
        case VLabelLit(x)     => LabelLit(x)
        case VNe(head, spine) => spine.quoteWithUnfold(head.quote)
        case VGlobal(head, lvl, spine, _) =>
          spine.quoteWithUnfold(Global(head, lvl))
        case VPair(fst, snd) => Pair(fst.quoteWithUnfold, snd.quoteWithUnfold)
        case VLam(bind, icit, body) =>
          Lam(bind, icit, body(VVar(k)).quoteWithUnfold(k + 1, unfold))
        case VPi(bind, icit, ty, u1, body, u2) =>
          Pi(
            bind,
            icit,
            ty.quoteWithUnfold,
            u1.quote,
            body(VVar(k)).quoteWithUnfold(k + 1, unfold),
            u2.quote
          )
        case VPiLvl(x, body, u) =>
          val v = VFinLevel.vr(k)
          PiLvl(x, body(v).quoteWithUnfold(k + 1, unfold), u(v).quote(k + 1))
        case VLamLvl(x, body) =>
          LamLvl(x, body(VFinLevel.vr(k)).quoteWithUnfold(k + 1, unfold))
        case VSigma(bind, ty, u1, body, u2) =>
          Sigma(
            bind,
            ty.quoteWithUnfold,
            u1.quote,
            body(VVar(k)).quoteWithUnfold(k + 1, unfold),
            u2.quote
          )

    def quote(implicit k: Lvl): Tm = quoteWithUnfold(k, UnfoldMetas)
