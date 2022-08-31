import Common.*
import Core.*
import Errors.*

import scala.annotation.tailrec
import scala.collection.immutable.IntMap

object Value:
  // universe level values
  final case class VFinLevel(
      k: Int,
      vars: IntMap[Int] = IntMap.empty,
      metas: IntMap[Int] = IntMap.empty
  ):
    def max(o: VFinLevel): VFinLevel =
      VFinLevel(
        k max o.k,
        vars.unionWith(o.vars, (_, a, b) => a max b),
        metas.unionWith(o.metas, (_, a, b) => a max b)
      )
    def +(o: Int): VFinLevel =
      VFinLevel(
        k + o,
        vars.map((k, v) => k -> (v + o)),
        metas.map((k, v) => k -> (v + o))
      )
    def -(o: Int): Option[VFinLevel] =
      if k < o || vars.exists((_, k) => k < o) ||
        metas.exists((_, k) => k < o)
      then None
      else
        Some(
          VFinLevel(
            k - o,
            vars.map((key, k) => key -> (k - o)),
            metas.map((key, k) => key -> (k - o))
          )
        )
  object VFinLevel:
    val unit: VFinLevel = VFinLevel(0, IntMap.empty, IntMap.empty)
    def vr(l: Lvl): VFinLevel =
      VFinLevel(0, IntMap.singleton(l.expose, 0), IntMap.empty)
    def meta(id: LMetaId): VFinLevel =
      VFinLevel(0, IntMap.empty, IntMap.singleton(id.expose, 0))

  object VFinLevelVar:
    def apply(m: Lvl, k: Int) =
      VFinLevel(0, IntMap.singleton(m.expose, k), IntMap.empty)
    def unapply(value: VFinLevel): Option[(Lvl, Int)] = value match
      case VFinLevel(0, vars, metas) if metas.isEmpty && vars.size == 1 =>
        val m = vars.keys.head
        Some((mkLvl(m), vars(m)))
      case _ => None

  object VFinLevelMeta:
    def apply(m: LMetaId, k: Int) =
      VFinLevel(0, IntMap.empty, IntMap.singleton(m.expose, k))
    def unapply(value: VFinLevel): Option[(LMetaId, Int)] = value match
      case VFinLevel(0, vars, metas) if vars.isEmpty && metas.size == 1 =>
        val m = metas.keys.head
        Some((lmetaId(m), metas(m)))
      case _ => None

  object VFinLevelNat:
    def apply(k: Int) =
      VFinLevel(k, IntMap.empty, IntMap.empty)
    def unapply(value: VFinLevel): Option[Int] = value match
      case VFinLevel(k, vars, metas) if vars.isEmpty && metas.isEmpty => Some(k)
      case _                                                          => None

  enum VLevel:
    case VOmega
    case VOmega1
    case VFL(lvl: VFinLevel)

    def max(o: VLevel): VLevel = (this, o) match
      case (VFL(a), VFL(b)) => VFL(a max b)
      case (VOmega1, _)     => VOmega1
      case (_, VOmega1)     => VOmega1
      case _                => VOmega

    def inc: VLevel = this match
      case VOmega1 => throw Impossible
      case VOmega  => VOmega1
      case VFL(l)  => VFL(l + 1)
  export VLevel.*
  object VLevel:
    val unit: VLevel = VFL(VFinLevel.unit)
    def vr(l: Lvl): VLevel = VFL(VFinLevel.vr(l))

  // values
  type Env = List[Either[VFinLevel, Val]]

  enum Clos[A]:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: A => Val)
  export Clos.*

  final case class ClosLvl(env: Env, tm: Level)

  enum Head:
    case HVar(lvl: Lvl)
    case HPrim(name: PrimName)
    case HMeta(id: MetaId)
  export Head.*

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SAppLvl(spine: Spine, arg: VFinLevel)
    case SProj(spine: Spine, proj: ProjType)
    case SPrim(
        spine: Spine,
        name: PrimName,
        args: List[Either[VFinLevel, (Val, Icit)]]
    )

    def size: Int =
      @tailrec
      def go(sp: Spine, i: Int): Int = sp match
        case SId             => 0
        case SApp(sp, _, _)  => go(sp, i + 1)
        case SAppLvl(sp, _)  => go(sp, i + 1)
        case SProj(sp, _)    => go(sp, i + 1)
        case SPrim(sp, _, _) => go(sp, i + 1)
      go(this, 0)
  export Spine.*

  type VTy = Val

  enum Val:
    case VNe(head: Head, spine: Spine)
    case VGlobal(name: Name, lvl: Lvl, spine: Spine, value: () => Val)
    case VType(lvl: VLevel)
    case VLam(bind: Bind, icit: Icit, body: Clos[Val])
    case VPi(
        bind: Bind,
        icit: Icit,
        ty: VTy,
        u1: VLevel,
        body: Clos[Val],
        u2: VLevel
    )
    case VLamLvl(bind: Bind, body: Clos[VFinLevel])
    case VPiLvl(name: Bind, body: Clos[VFinLevel], u: ClosLvl)
    case VSigma(bind: Bind, ty: VTy, u1: VLevel, body: Clos[Val], u2: VLevel)
    case VPair(fst: Val, snd: Val)
    case VLabelLit(name: Name)
  export Val.*

  def vlam(x: String, body: Val => Val): Val =
    VLam(DoBind(Name(x)), Expl, CFun(body))
  def vlami(x: String, body: Val => Val): Val =
    VLam(DoBind(Name(x)), Impl, CFun(body))
  def vlamlvl(x: String, body: VFinLevel => Val): Val =
    VLamLvl(DoBind(Name(x)), CFun(body))

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

  object VPrim:
    def apply(x: PrimName, sp: Spine = SId) = VNe(HPrim(x), sp)
    def unapply(value: Val): Option[(PrimName, Spine)] = value match
      case VNe(HPrim(x), spine) => Some((x, spine))
      case _                    => None

  object VUnitType:
    def apply() = VNe(HPrim(PUnitType), SId)
    def unapply(value: Val): Boolean = value match
      case VNe(HPrim(PUnitType), SId) => true
      case _                          => false

  object VUnit:
    def apply() = VNe(HPrim(PUnit), SId)
    def unapply(value: Val): Boolean = value match
      case VNe(HPrim(PUnit), SId) => true
      case _                      => false

  object VLabel:
    def apply() = VNe(HPrim(PLabel), SId)
    def unapply(value: Val): Boolean = value match
      case VNe(HPrim(PLabel), SId) => true
      case _                       => false

  object VEnum:
    def apply() = VNe(HPrim(PEnum), SId)
    def unapply(value: Val): Boolean = value match
      case VNe(HPrim(PEnum), SId) => true
      case _                      => false

  object VENil:
    def apply() = VNe(HPrim(PENil), SId)
    def unapply(value: Val): Boolean = value match
      case VNe(HPrim(PENil), SId) => true
      case _                      => false

  object VLift:
    def apply(k: VFinLevel, l: VFinLevel, a: Val) =
      VNe(HPrim(PLift), SApp(SAppLvl(SAppLvl(SId, k), l), a, Expl))
    def unapply(value: Val): Option[(VFinLevel, VFinLevel, Val)] = value match
      case VNe(HPrim(PLift), SApp(SAppLvl(SAppLvl(SId, k), l), a, Expl)) =>
        Some((k, l, a))
      case _ => None

  object VLiftTerm:
    def apply(k: VFinLevel, l: VFinLevel, a: Val, t: Val) =
      VNe(
        HPrim(PLiftTerm),
        SApp(SApp(SAppLvl(SAppLvl(SId, k), l), a, Impl), t, Expl)
      )
    def unapply(value: Val): Option[(VFinLevel, VFinLevel, Val, Val)] =
      value match
        case VNe(
              HPrim(PLiftTerm),
              SApp(SApp(SAppLvl(SAppLvl(SId, k), l), a, Impl), t, Expl)
            ) =>
          Some((k, l, a, t))
        case _ => None

  object VECons:
    def apply(hd: Val, tl: Val) =
      VNe(HPrim(PECons), SApp(SApp(SId, hd, Expl), tl, Expl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VNe(HPrim(PECons), SApp(SApp(SId, hd, Expl), tl, Expl)) =>
        Some((hd, tl))
      case _ => None

  object VTZ:
    def apply(l: Val, e: Val) =
      VNe(HPrim(PTZ), SApp(SApp(SId, l, Impl), e, Impl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VNe(HPrim(PTZ), SApp(SApp(SId, l, Impl), e, Impl)) =>
        Some((l, e))
      case _ => None

  object VTS:
    def apply(l: Val, e: Val, t: Val) =
      VNe(HPrim(PTS), SApp(SApp(SApp(SId, l, Impl), e, Impl), t, Expl))
    def unapply(value: Val): Option[(Val, Val, Val)] = value match
      case VNe(HPrim(PTS), SApp(SApp(SApp(SId, l, Impl), e, Impl), t, Expl)) =>
        Some((l, e, t))
      case _ => None
