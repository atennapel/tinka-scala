import Common.*
import Core.*
import Value.*
import Metas.*
import Errors.*
import Debug.*

object Evaluation:
  extension (c: Clos) def apply(v: Val): Val = c.tm.eval(v :: c.env)

  private def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _)   => v
    case Unsolved(_, _) => VMeta(id)

  private def vcheck(id: CheckId)(implicit env: Env): Val = getCheck(id) match
    case Unchecked(ctx, t, a, m) => vappPruning(vmeta(m), ctx.pruning)
    case Checked(t)              => t.eval

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (Nil, Nil)                => v
      case (t :: env, Some(i) :: pr) => vappPruning(v, pr)(env)(t, i)
      case (_ :: env, None :: pr)    => vappPruning(v, pr)(env)
      case _                         => throw Impossible

  extension (c: Tm)
    def eval(implicit env: Env): Val = c match
      case Type                     => VType
      case UnitType                 => VUnitType
      case Unit                     => VUnit
      case Var(ix)                  => ix.index(env)
      case Let(_, _, value, body)   => body.eval(value.eval :: env)
      case App(fn, arg, icit)       => fn.eval(env)(arg.eval, icit)
      case Pi(bind, icit, ty, body) => VPi(bind, icit, ty.eval, Clos(env, body))
      case Sigma(bind, ty, body)    => VSigma(bind, ty.eval, Clos(env, body))
      case Lam(bind, icit, body)    => VLam(bind, icit, Clos(env, body))
      case Pair(fst, snd)           => VPair(fst.eval, snd.eval)
      case Proj(tm, proj)           => tm.eval.proj(proj)
      case Meta(id)                 => vmeta(id)
      case AppPruning(tm, pr)       => vappPruning(tm.eval, pr)
      case PostponedCheck(c)        => vcheck(c)

    def nf: Tm = c.eval(Nil).quote(lvl0)

  extension (hd: Head)
    def quote(implicit k: Lvl): Tm = hd match
      case HVar(lvl) => Var(lvl.toIx)
      case HMeta(id) => Meta(id)

  extension (sp: Spine)
    def quote(hd: Tm)(implicit k: Lvl): Tm = sp match
      case SId                 => hd
      case SApp(sp, arg, icit) => App(sp.quote(hd), arg.quote, icit)
      case SProj(sp, proj)     => Proj(sp.quote(hd), proj)

  extension (v: Val)
    def apply(arg: Val, icit: Icit): Val = v match
      case VLam(_, _, body) => body(arg)
      case VNe(hd, sp)      => VNe(hd, SApp(sp, arg, icit))
      case _                => throw Impossible

    def apply(sp: Spine): Val = sp match
      case SId            => v
      case SApp(sp, a, i) => v(sp)(a, i)
      case SProj(sp, p)   => v(sp).proj(p)

    def force: Val = v match
      case VNe(HMeta(m), sp) =>
        getMeta(m) match
          case Solved(v, _)   => (v(sp)).force
          case Unsolved(_, _) => v
      case _ => v

    def proj(proj: ProjType): Val = (v, proj) match
      case (VPair(fst, _), Fst)         => fst
      case (VPair(_, snd), Snd)         => snd
      case (VPair(fst, _), Named(_, 0)) => fst
      case (VPair(_, snd), Named(x, i)) => snd.proj(Named(x, i - 1))
      case (VNe(hd, sp), _)             => VNe(hd, SProj(sp, proj))
      case _                            => throw Impossible

    def quote(implicit k: Lvl): Tm = v.force match
      case VType                  => Type
      case VUnitType              => UnitType
      case VUnit                  => Unit
      case VNe(head, spine)       => spine.quote(head.quote)
      case VPair(fst, snd)        => Pair(fst.quote, snd.quote)
      case VLam(bind, icit, body) => Lam(bind, icit, body(VVar(k)).quote(k + 1))
      case VPi(bind, icit, ty, body) =>
        Pi(bind, icit, ty.quote, body(VVar(k)).quote(k + 1))
      case VSigma(bind, ty, body) =>
        Sigma(bind, ty.quote, body(VVar(k)).quote(k + 1))
