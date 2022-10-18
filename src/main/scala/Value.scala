import Common.*
import Syntax.{Tm, ProjType}

import scala.annotation.tailrec

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

    def size: Int =
      @tailrec
      def go(sp: Spine, i: Int): Int = sp match
        case SId            => 0
        case SApp(sp, _, _) => go(sp, i + 1)
        case SProj(sp, _)   => go(sp, i + 1)
      go(this, 0)
  export Spine.*

  enum Val:
    case VType
    case VRigid(hd: Lvl, spine: Spine)
    case VFlex(hd: MetaId, spine: Spine)
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

  object VMeta:
    def apply(id: MetaId) = VFlex(id, SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VFlex(head, SId) => Some(head)
      case _                => None
