import Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Type
    case Var(ix: Ix)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Lam(bind: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)
    case Pi(bind: Bind, ty: Ty, body: Ty)
  export Tm.*
