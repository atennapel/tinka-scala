import Common.*
import Core.*

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)

  enum Head:
    case HVar(lvl: Lvl)
  export Head.*

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val)
  export Spine.*

  type VTy = Val

  enum Val:
    case VNe(head: Head, spine: Spine)
    case VType
    case VLam(bind: Bind, body: Clos)
    case VPi(bind: Bind, ty: VTy, body: Clos)
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
