import Common.*
import Core.*
import Value.*
import Errors.*

object Evaluation:
  extension (c: Clos) def apply(v: Val): Val = c.tm.eval(v :: c.env)

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

    def nf: Tm = c.eval(Nil).quote(lvl0)

  extension (hd: Head)
    def quote(implicit k: Lvl): Tm = hd match
      case HVar(lvl) => Var(lvl.toIx)

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

    def proj(proj: ProjType): Val = (v, proj) match
      case (VPair(fst, _), Fst)         => fst
      case (VPair(_, snd), Snd)         => snd
      case (VPair(fst, _), Named(_, 0)) => fst
      case (VPair(_, snd), Named(x, i)) => snd.proj(Named(x, i - 1))
      case (VNe(hd, sp), _)             => VNe(hd, SProj(sp, proj))
      case _                            => throw Impossible

    def quote(implicit k: Lvl): Tm = v match
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
