import Common.*
import Core.*
import Value.*
import Errors.*

object Evaluation:
  extension (c: Clos) def apply(v: Val): Val = c.tm.eval(v :: c.env)

  extension (c: Tm)
    def eval(implicit env: Env): Val = c match
      case Type                   => VType
      case UnitType               => VUnitType
      case Unit                   => VUnit
      case Var(ix)                => ix.index(env)
      case Let(_, _, value, body) => body.eval(value.eval :: env)
      case App(fn, arg)           => fn.eval(env)(arg.eval)
      case Pi(bind, ty, body)     => VPi(bind, ty.eval, Clos(env, body))
      case Sigma(bind, ty, body)  => VSigma(bind, ty.eval, Clos(env, body))
      case Lam(bind, body)        => VLam(bind, Clos(env, body))
      case Pair(fst, snd)         => VPair(fst.eval, snd.eval)
      case Proj(tm, proj)         => tm.eval.proj(proj)

    def nf: Tm = c.eval(Nil).quote(lvl0)

  extension (hd: Head)
    def quote(implicit k: Lvl): Tm = hd match
      case HVar(lvl) => Var(lvl.toIx)

  extension (sp: Spine)
    def quote(hd: Tm)(implicit k: Lvl): Tm = sp match
      case SId             => hd
      case SApp(sp, arg)   => App(sp.quote(hd), arg.quote)
      case SProj(sp, proj) => Proj(sp.quote(hd), proj)

  extension (v: Val)
    def apply(arg: Val): Val = v match
      case VLam(_, body) => body(arg)
      case VNe(hd, sp)   => VNe(hd, SApp(sp, arg))
      case _             => throw Impossible

    def proj(proj: ProjType): Val = (v, proj) match
      case (VPair(fst, _), Fst)         => fst
      case (VPair(_, snd), Snd)         => snd
      case (VPair(fst, _), Named(_, 0)) => fst
      case (VPair(_, snd), Named(x, i)) => snd.proj(Named(x, i - 1))
      case (VNe(hd, sp), _)             => VNe(hd, SProj(sp, proj))
      case _                            => throw Impossible

    def quote(implicit k: Lvl): Tm = v match
      case VType               => Type
      case VUnitType           => UnitType
      case VUnit               => Unit
      case VNe(head, spine)    => spine.quote(head.quote)
      case VPair(fst, snd)     => Pair(fst.quote, snd.quote)
      case VLam(bind, body)    => Lam(bind, body(VVar(k)).quote(k + 1))
      case VPi(bind, ty, body) => Pi(bind, ty.quote, body(VVar(k)).quote(k + 1))
      case VSigma(bind, ty, body) =>
        Sigma(bind, ty.quote, body(VVar(k)).quote(k + 1))
