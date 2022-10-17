import Common.*
import Syntax.{Tm, ProjType}

object Value:
  type VTy = Val

  type Env = List[Val]

  extension (e: Env) def apply(i: Ix): Val = i(e)

  final case class Clos private (env: Env, tm: Tm)
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = new Clos(env, tm)

  enum Spine:
    case SId
    case SApp(fn: Spine, arg: Val, icit: Icit)
    case SProj(hd: Spine, proj: ProjType)
  export Spine.*

  enum Val:
    case VType
    case VRigid(hd: Lvl, spine: Spine)
    case VUri(uri: String, spine: Spine, value: () => Val)

    case VLam(bind: Bind, icit: Icit, body: Clos)
    case VPi(bind: Bind, icit: Icit, ty: VTy, body: Clos)

    case VPair(fst: Val, snd: Val)
    case VSigma(bind: Bind, ty: VTy, body: Clos)

    case VUnitType
    case VUnitValue
  export Val.*

  object VVar:
    def apply(lvl: Lvl) = VRigid(lvl, SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(head, SId) => Some(head)
      case _                 => None
