import Common.*
import Core.*
import Value.*
import Errors.*

object Evaluation:
  extension (c: Clos) def apply(v: Val): Val = c.tm.eval(v :: c.env)

  extension (c: Tm)
    def eval(implicit env: Env): Val = c match
      case Var(ix)                => ix.index(env)
      case Let(_, _, value, body) => body.eval(value.eval :: env)
      case Type                   => VType
      case Pi(bind, ty, body)     => VPi(bind, ty.eval, Clos(env, body))
      case Sigma(bind, ty, body)  => VSigma(bind, ty.eval, Clos(env, body))
      case App(fn, arg)           => fn.eval(env)(arg.eval)
      case Lam(bind, body)        => VLam(bind, Clos(env, body))
      case UnitType               => VUnitType
      case Unit                   => VUnit

    def nf: Tm = c.eval(Nil).quote(lvl0)

  extension (hd: Head)
    def quote(implicit k: Lvl): Tm = hd match
      case HVar(lvl) => Var(lvl.toIx)

  extension (sp: Spine)
    def quote(hd: Tm)(implicit k: Lvl): Tm = sp match
      case SId           => hd
      case SApp(sp, arg) => App(sp.quote(hd), arg.quote)

  extension (v: Val)
    def apply(arg: Val): Val = v match
      case VLam(_, body) => body(arg)
      case VNe(hd, sp)   => VNe(hd, SApp(sp, arg))
      case _             => throw Impossible

    def quote(implicit k: Lvl): Tm = v match
      case VNe(head, spine)    => spine.quote(head.quote)
      case VType               => Type
      case VLam(bind, body)    => Lam(bind, body(VVar(k)).quote(k + 1))
      case VPi(bind, ty, body) => Pi(bind, ty.quote, body(VVar(k)).quote(k + 1))
      case VSigma(bind, ty, body) =>
        Sigma(bind, ty.quote, body(VVar(k)).quote(k + 1))
      case VUnitType => UnitType
      case VUnit     => Unit
