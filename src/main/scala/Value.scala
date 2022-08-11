import Common.*
import Core.*

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)

  enum Head:
    case HVar(lvl: Lvl)
    case HMeta(id: MetaId)
  export Head.*

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SProj(spine: Spine, proj: ProjType)
  export Spine.*

  type VTy = Val

  enum Val:
    case VNe(head: Head, spine: Spine)
    case VType
    case VLam(bind: Bind, icit: Icit, body: Clos)
    case VPi(bind: Bind, icit: Icit, ty: VTy, body: Clos)
    case VSigma(bind: Bind, ty: VTy, body: Clos)
    case VPair(fst: Val, snd: Val)
    case VUnitType
    case VUnit
  export Val.*

  object VVar:
    def apply(lvl: Lvl) = VNe(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VNe(HVar(head), SId) => Some(head)
      case _                    => None

  object VMeta:
    def apply(id: MetaId) = VNe(HMeta(id), SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VNe(HMeta(head), SId) => Some(head)
      case _                     => None
