import Common.*

object Core:
  type Ty = Tm

  enum Tm:
    case Var(ix: Ix)
    case Let(bind: Bind, ty: Ty, value: Tm, body: Tm)
    case Type

    case Pi(bind: Bind, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm)
    case Lam(bind: Bind, body: Ty)
  export Tm.*
