import Common.*
import Core.Tm

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)

  type Spine = List[Elim]
  enum Elim:
    case EApp(arg: Val)

  enum Val:
    case VNe(head: Lvl, spine: Spine)
    case VType

    case VLam(name: Name, body: Clos)
    case VPi(name: Name, ty: () => Val, body: Clos)

  object VPi:
    def apply(name: Name, ty: => Val, body: Clos) =
      Val.VPi(name, () => ty, body)

  object VVar:
    import Val.VNe
    def apply(lvl: Lvl) = VNe(lvl, List.empty)
    def unapply(value: Val): Option[Lvl] = value match
      case VNe(head, List()) => Some(head)
      case _                 => None
