import Common.*
import Syntax.Tm

object Value:
  type VTy = Val

  type Env = List[Val]

  extension (e: Env) def apply(i: Ix): Val = i(e)

  final case class Clos private (env: Env, tm: Tm)
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = new Clos(env, tm)

  enum Spine:
    case SId
    case SApp(fn: Spine, arg: Val)
  export Spine.*

  enum Val:
    case VType
    case VRigid(hd: Lvl, spine: Spine)

    case VLam(bind: Bind, body: Clos)
    case VPi(bind: Bind, ty: VTy, body: Clos)
  export Val.*

  object VVar:
    def apply(lvl: Lvl) = VRigid(lvl, SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(head, SId) => Some(head)
      case _                 => None
