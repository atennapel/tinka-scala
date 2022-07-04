import Core.{Tm as CTm}
import Core.Tm as C
import Surface.*
import Surface.Tm.*
import Common.*

object Pretty:
  private def prettyTm(tm: CTm, ns: List[Name]): Tm = tm match
    case C.Var(ix)      => Var(ixEnv(ns, ix))
    case C.Global(name) => Var(name)
    case C.App(fn, arg) => App(prettyTm(fn, ns), prettyTm(arg, ns))
    case C.Type         => Type
    case C.Let(x0, ty, value, b) =>
      val x = freshName(x0, ns)
      Let(x, Some(prettyTm(ty, ns)), prettyTm(value, ns), prettyTm(b, x :: ns))
    case C.Pi(x0, ty, b) =>
      val x = freshName(x0, ns)
      Pi(x, prettyTm(ty, ns), prettyTm(b, x :: ns))
    case C.Lam(x0, b) =>
      val x = freshName(x0, ns)
      Lam(x, prettyTm(b, x :: ns))

  def pretty(tm: CTm, ns: List[Name] = List.empty): String =
    prettyTm(tm, ns).toString
