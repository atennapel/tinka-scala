import Common.*

object Surface:
  type Ty = Tm

  enum Tm:
    case Var(name: Name)
    case Let(bind: Bind, ty: Option[Ty], value: Tm, body: Tm)
    case Type

    case Pi(bind: Bind, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm)
    case Lam(bind: Bind, ty: Option[Ty], body: Ty)
  export Tm.*
