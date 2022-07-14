import Common.*
import Core.*

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)

  enum Head:
    case HVar(lvl: Lvl)
    case HMeta(id: MetaId)
    case HPrim(name: PrimName)

  type Spine = List[Elim]
  enum Elim:
    case EApp(arg: Val, icit: Icit)
    case EProj(proj: ProjType)

  enum Val:
    case VNe(head: Head, spine: Spine)
    case VGlobal(head: Name, spine: Spine, value: () => Val)
    case VType

    case VLam(name: Name, icit: Icit, body: Clos)
    case VPi(name: Name, icit: Icit, ty: Val, body: Clos)

    case VSigma(name: Name, ty: Val, body: Clos)
    case VPair(fst: Val, snd: Val)

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

  object VPrim:
    import Val.VNe
    import Head.HPrim
    def apply(name: PrimName) = VNe(HPrim(name), List.empty)
    def unapply(value: Val): Option[PrimName] = value match
      case VNe(HPrim(head), Nil) => Some(head)
      case _                     => None
