import Common.*
import Core.Tm

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)

  enum Head:
    case HVar(lvl: Lvl)
    case HMeta(id: MetaId)

  type Spine = List[Elim]
  enum Elim:
    case EApp(arg: Val, icit: Icit)

  enum Val:
    case VNe(head: Head, spine: Spine)
    case VGlobal(head: Name, spine: Spine, value: () => Val)
    case VType

    case VLam(name: Name, icit: Icit, body: Clos)
    case VPi(name: Name, icit: Icit, ty: Val, body: Clos)

    case VSigma(name: Name, ty: Val, body: Clos)

  object VVar:
    import Val.VNe
    import Head.HVar
    def apply(lvl: Lvl) = VNe(HVar(lvl), List.empty)
    def unapply(value: Val): Option[Lvl] = value match
      case VNe(HVar(head), Nil) => Some(head)
      case _                    => None

  object VMeta:
    import Val.VNe
    import Head.HMeta
    def apply(id: MetaId) = VNe(HMeta(id), List.empty)
    def unapply(value: Val): Option[MetaId] = value match
      case VNe(HMeta(head), Nil) => Some(head)
      case _                     => None
