import Common.*

object Presyntax:
  type RTy = RTm
  enum RTm:
    case RType
    case RVar(name: Name)
    case RLet(name: Name, ty: Option[RTy], value: RTm, body: RTm)

    case RLam(bind: Bind, ty: Option[RTy], body: RTm)
    case RApp(fn: RTm, arg: RTm)
    case RPi(bind: Bind, ty: RTy, body: RTy)
  export RTm.*
