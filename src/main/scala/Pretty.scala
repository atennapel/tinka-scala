import Core.{Tm as CTm}
import Core.Tm as C
import Surface.*
import Surface.Tm.*
import Common.*

object Pretty:
  def pretty(tm: CTm, ns: List[Name] = List.empty): Tm = tm match
    case C.Var(ix)      => Var(ixEnv(ns, ix))
    case C.Global(name) => Var(name)
    case C.App(fn, arg) => App(pretty(fn, ns), pretty(arg, ns))
    case C.Type         => Type
    case C.Let(x0, ty, value, b) =>
      val x = freshName(x0, ns)
      Let(x, Some(pretty(ty, ns)), pretty(value, ns), pretty(b, x :: ns))
    case C.Pi(x0, ty, b) =>
      val x = freshName(x0, ns)
      Pi(x, pretty(ty, ns), pretty(b, x :: ns))
    case C.Lam(x0, b) =>
      val x = freshName(x0, ns)
      Lam(x, pretty(b, x :: ns))
