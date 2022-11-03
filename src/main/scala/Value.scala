import Common.*
import Syntax.{Level, Tm, ProjType}

import scala.collection.immutable.IntMap
import scala.annotation.tailrec

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
      case VOmega1 => impossible()
      case VOmega  => VOmega1
      case VFL(l)  => VFL(l + 1)
  export VLevel.*

  object VLevel:
    val unit: VLevel = VFL(VFinLevel.unit)
    def vr(l: Lvl): VLevel = VFL(VFinLevel.vr(l))

  // values
  type VTy = Val

  enum Env:
    case EEmpty
    case EVal(env: Env, value: Val)
    case ELevel(env: Env, level: VFinLevel)

    def tail: Env = this match
      case EVal(env, _)   => env
      case ELevel(env, _) => env
      case _              => impossible()
  export Env.*

  extension (e: Env)
    @tailrec
    def apply(i: Ix): Either[VFinLevel, Val] = e match
      case EVal(env, value) if i.expose == 0 => Right(value)
      case ELevel(env, lvl) if i.expose == 0 => Left(lvl)
      case EVal(env, _)                      => env(mkIx(i.expose - 1))
      case ELevel(env, _)                    => env(mkIx(i.expose - 1))
      case _                                 => impossible()

  enum Clos[A]:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: A => Val)
  export Clos.*

  object Clos:
    def apply[A](tm: Tm)(implicit env: Env): Clos[A] = CClos(env, tm)

  final case class ClosLvl(env: Env, tm: Level)

  enum Spine:
    case SId
    case SApp(fn: Spine, arg: Val, icit: Icit)
    case SAppLvl(fn: Spine, arg: VFinLevel)
    case SProj(hd: Spine, proj: ProjType)

    def size: Int =
      @tailrec
      def go(sp: Spine, i: Int): Int = sp match
        case SId            => 0
        case SApp(sp, _, _) => go(sp, i + 1)
        case SAppLvl(sp, _) => go(sp, i + 1)
        case SProj(sp, _)   => go(sp, i + 1)
      go(this, 0)
  export Spine.*

  enum Head:
    case HVar(lvl: Lvl)
  export Head.*

  enum Val:
    case VType(lvl: VLevel)
    case VRigid(hd: Head, spine: Spine)
    case VFlex(hd: MetaId, spine: Spine)

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

    case VPair(fst: Val, snd: Val)
    case VSigma(bind: Bind, ty: VTy, u1: VLevel, body: Clos[Val], u2: VLevel)
  export Val.*

  private def bind(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vpiE(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VPi(bind(x), Expl, ty, u1, CFun(fn), u2)
  def vpiI(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VPi(bind(x), Impl, ty, u1, CFun(fn), u2)
  def vfun(ty: Val, u1: VLevel, u2: VLevel, rt: Val): Val =
    VPi(DontBind, Expl, ty, u1, CFun(_ => rt), u2)
  def vlamE(x: String, fn: Val => Val): Val = VLam(bind(x), Expl, CFun(fn))
  def vlamI(x: String, fn: Val => Val): Val =
    VLam(bind(x), Impl, CFun(fn))
  def vsigma(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VSigma(bind(x), ty, u1, CFun(fn), u2)

  object VVar:
    def apply(lvl: Lvl) = VRigid(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(HVar(head), SId) => Some(head)
      case _                       => None

  object VMeta:
    def apply(id: MetaId) = VFlex(id, SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VFlex(head, SId) => Some(head)
      case _                => None
