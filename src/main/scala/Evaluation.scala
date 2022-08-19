import Common.*
import Core.*
import Value.*
import Metas.*
import Errors.*
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
      case (Nil, Nil)                       => v
      case (Right(t) :: env, Some(i) :: pr) => vappPruning(v, pr)(env)(t, i)
      case (_ :: env, None :: pr)           => vappPruning(v, pr)(env)
      case _                                => throw Impossible

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
      case Type(l)                => VType(l.eval)
      case UnitType               => VUnitType
      case Unit                   => VUnit
      case Var(ix)                => ix.index(env).toOption.get
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

    def nf: Tm = c.eval(Nil).quote(lvl0)

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
      case HMeta(id) => Meta(id)

  extension (sp: Spine)
    def quote(hd: Tm)(implicit k: Lvl): Tm = sp match
      case SId                 => hd
      case SApp(sp, arg, icit) => App(sp.quote(hd), arg.quote, icit)
      case SAppLvl(sp, arg)    => AppLvl(sp.quote(hd), arg.quote)
      case SProj(sp, proj)     => Proj(sp.quote(hd), proj)

  extension (v: Val)
    def apply(arg: Val, icit: Icit): Val = v match
      case VLam(_, _, body) => body(arg)
      case VNe(hd, sp)      => VNe(hd, SApp(sp, arg, icit))
      case _                => throw Impossible

    def apply(arg: VFinLevel): Val = v match
      case VLamLvl(_, body) => body(arg)
      case VNe(hd, sp)      => VNe(hd, SAppLvl(sp, arg))
      case _                => throw Impossible

    def apply(sp: Spine): Val = sp match
      case SId            => v
      case SApp(sp, a, i) => v(sp)(a, i)
      case SAppLvl(sp, a) => v(sp)(a)
      case SProj(sp, p)   => v(sp).proj(p)

    def force: Val = v match
      case VNe(HMeta(m), sp) =>
        getMeta(m) match
          case Solved(v, _, _) => (v(sp)).force
          case Unsolved(_, _)  => v
      case _ => v

    def proj(proj: ProjType): Val = (v, proj) match
      case (VPair(fst, _), Fst)         => fst
      case (VPair(_, snd), Snd)         => snd
      case (VPair(fst, _), Named(_, 0)) => fst
      case (VPair(_, snd), Named(x, i)) => snd.proj(Named(x, i - 1))
      case (VNe(hd, sp), _)             => VNe(hd, SProj(sp, proj))
      case _                            => throw Impossible

    def quote(implicit k: Lvl): Tm = v.force match
      case VType(l)               => Type(l.quote)
      case VUnitType              => UnitType
      case VUnit                  => Unit
      case VNe(head, spine)       => spine.quote(head.quote)
      case VPair(fst, snd)        => Pair(fst.quote, snd.quote)
      case VLam(bind, icit, body) => Lam(bind, icit, body(VVar(k)).quote(k + 1))
      case VPi(bind, icit, ty, u1, body, u2) =>
        Pi(bind, icit, ty.quote, u1.quote, body(VVar(k)).quote(k + 1), u2.quote)
      case VPiLvl(x, body, u) =>
        val v = VFinLevel.vr(k)
        PiLvl(x, body(v).quote(k + 1), u(v).quote(k + 1))
      case VLamLvl(x, body) => LamLvl(x, body(VFinLevel.vr(k)).quote(k + 1))
      case VSigma(bind, ty, u1, body, u2) =>
        Sigma(bind, ty.quote, u1.quote, body(VVar(k)).quote(k + 1), u2.quote)
