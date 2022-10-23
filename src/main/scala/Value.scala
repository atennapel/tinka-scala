import Common.*
import Syntax.{Tm, ProjType}

import scala.annotation.tailrec

object Value:
  type VTy = Val

  type Env = List[Val]

  extension (e: Env) def apply(i: Ix): Val = i(e)

  enum Clos:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: Val => Val)
  export Clos.*
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = CClos(env, tm)

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

  enum Head:
    case HVar(lvl: Lvl)
    case HPrim(name: PrimName)
  export Head.*

  enum Val:
    case VType
    case VRigid(hd: Head, spine: Spine)
    case VFlex(hd: MetaId, spine: Spine)
    case VUri(uri: String, spine: Spine, value: () => Val)

    case VLam(bind: Bind, icit: Icit, body: Clos)
    case VPi(bind: Bind, icit: Icit, ty: VTy, body: Clos)

    case VPair(fst: Val, snd: Val)
    case VSigma(bind: Bind, ty: VTy, body: Clos)
  export Val.*

  private def bind(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vpiE(x: String, ty: Val, fn: Val => Val): Val =
    VPi(bind(x), Expl, ty, CFun(fn))
  def vpiI(x: String, ty: Val, fn: Val => Val): Val =
    VPi(bind(x), Impl, ty, CFun(fn))
  def vfun(ty: Val, rt: Val): Val = VPi(DontBind, Expl, ty, CFun(_ => rt))
  def vlamE(x: String, fn: Val => Val): Val = VLam(bind(x), Expl, CFun(fn))
  def vlamI(x: String, fn: Val => Val): Val =
    VLam(bind(x), Impl, CFun(fn))
  def vsigma(x: String, ty: Val, fn: Val => Val): Val =
    VSigma(bind(x), ty, CFun(fn))

  object VVar:
    def apply(lvl: Lvl) = VRigid(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(HVar(head), SId) => Some(head)
      case _                       => None

  object VPrim:
    def apply(name: PrimName) = VRigid(HPrim(name), SId)
    def unapply(value: Val): Option[PrimName] = value match
      case VRigid(HPrim(head), SId) => Some(head)
      case _                        => None

  object VMeta:
    def apply(id: MetaId) = VFlex(id, SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VFlex(head, SId) => Some(head)
      case _                => None

  object VUnitValue:
    def apply() = VRigid(HPrim(PUnitValue), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnitValue), SId) => true
      case _                              => false

  object VUnitType:
    def apply() = VRigid(HPrim(PUnitType), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnitType), SId) => true
      case _                             => false

  object VVoid:
    def apply() = VRigid(HPrim(PVoid), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PVoid), SId) => true
      case _                         => false

  object VBool:
    def apply() = VRigid(HPrim(PBool), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PBool), SId) => true
      case _                         => false

  object VTrue:
    def apply() = VRigid(HPrim(PTrue), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PTrue), SId) => true
      case _                         => false

  object VFalse:
    def apply() = VRigid(HPrim(PFalse), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PFalse), SId) => true
      case _                          => false

  object VId:
    def apply(ta: Val, tb: Val, a: Val, b: Val) =
      VRigid(
        HPrim(PId),
        SApp(SApp(SApp(SApp(SId, ta, Impl), tb, Impl), a, Expl), b, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val, Val)] = value match
      case VRigid(
            HPrim(PId),
            SApp(SApp(SApp(SApp(SId, ta, Impl), tb, Impl), a, Expl), b, Expl)
          ) =>
        Some((ta, tb, a, b))
      case _ => None

  object VRefl:
    def apply(ta: Val, a: Val) =
      VRigid(
        HPrim(PId),
        SApp(SApp(SId, ta, Impl), a, Impl)
      )
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(
            HPrim(PId),
            SApp(SApp(SId, ta, Impl), a, Impl)
          ) =>
        Some((ta, a))
      case _ => None

  object VFix:
    def apply(ii: Val, f: Val, i: Val) =
      VRigid(
        HPrim(PFix),
        SApp(SApp(SApp(SId, ii, Impl), f, Expl), i, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val)] = value match
      case VRigid(
            HPrim(PFix),
            SApp(SApp(SApp(SId, ii, Impl), f, Expl), i, Expl)
          ) =>
        Some((ii, f, i))
      case _ => None

  object VRoll:
    def apply(ii: Val, f: Val, i: Val, x: Val) =
      VRigid(
        HPrim(PRoll),
        SApp(SApp(SApp(SApp(SId, ii, Impl), f, Impl), i, Impl), x, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val, Val)] = value match
      case VRigid(
            HPrim(PRoll),
            SApp(SApp(SApp(SApp(SId, ii, Impl), f, Impl), i, Impl), x, Expl)
          ) =>
        Some((ii, f, i, x))
      case _ => None
