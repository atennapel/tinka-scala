import Common.*
import Syntax.{Level, Tm, ProjType}

import scala.collection.immutable.IntMap
import scala.annotation.tailrec

object Value:
  // universe level values
  final case class VFinLevel(
      k: Int,
      vars: IntMap[Int] = IntMap.empty,
      metas: IntMap[(Int, List[VFinLevel])] = IntMap.empty
  ):
    def max(o: VFinLevel): VFinLevel =
      VFinLevel(
        k max o.k,
        vars.unionWith(o.vars, (_, a, b) => a max b),
        metas.unionWith(
          o.metas,
          { case (_, (a, s1), (b, s2)) =>
            (a max b, if s1 == s2 then s1 else impossible())
          }
        )
      )
    def +(o: Int): VFinLevel =
      VFinLevel(
        k + o,
        vars.map((k, v) => k -> (v + o)),
        metas.map { case (k, (v, sp)) => k -> (v + o, sp) }
      )
    def -(o: Int): Option[VFinLevel] =
      if k < o || vars.exists((_, k) => k < o) ||
        metas.exists { case (_, (k, _)) => k < o }
      then None
      else
        Some(
          VFinLevel(
            k - o,
            vars.map((key, k) => key -> (k - o)),
            metas.map { case (key, (k, sp)) => key -> (k - o, sp) }
          )
        )
  object VFinLevel:
    val unit: VFinLevel = VFinLevel(0, IntMap.empty, IntMap.empty)
    def vr(l: Lvl): VFinLevel =
      VFinLevel(0, IntMap.singleton(l.expose, 0), IntMap.empty)
    def meta(id: LMetaId, sp: List[VFinLevel] = Nil): VFinLevel =
      VFinLevel(0, IntMap.empty, IntMap.singleton(id.expose, (0, sp)))

  object VFinLevelVar:
    def apply(m: Lvl, k: Int) =
      VFinLevel(0, IntMap.singleton(m.expose, k), IntMap.empty)
    def unapply(value: VFinLevel): Option[(Lvl, Int)] = value match
      case VFinLevel(0, vars, metas) if metas.isEmpty && vars.size == 1 =>
        val m = vars.keys.head
        Some((mkLvl(m), vars(m)))
      case _ => None

  object VFinLevelMeta:
    def apply(m: LMetaId, k: Int, sp: List[VFinLevel]) =
      VFinLevel(0, IntMap.empty, IntMap.singleton(m.expose, (k, sp)))
    def unapply(value: VFinLevel): Option[(LMetaId, Int, List[VFinLevel])] =
      value match
        case VFinLevel(0, vars, metas) if vars.isEmpty && metas.size == 1 =>
          val m = metas.keys.head
          val (k, sp) = metas(m)
          Some((lmetaId(m), k, sp))
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

  enum Head:
    case HVar(lvl: Lvl)
    case HPrim(name: PrimName)
  export Head.*

  enum Val:
    case VType(lvl: VLevel)
    case VRigid(hd: Head, spine: Spine)
    case VFlex(hd: MetaId, spine: Spine)
    case VGlobal(uri: String, spine: Spine, value: () => Val)
    case VLabelLit(name: Name)

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

  // helpers
  private def bind(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vpiE(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VPi(bind(x), Expl, ty, u1, CFun(fn), u2)
  def vpiI(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VPi(bind(x), Impl(Unif), ty, u1, CFun(fn), u2)
  def vfun(ty: Val, u1: VLevel, u2: VLevel, rt: Val): Val =
    VPi(DontBind, Expl, ty, u1, CFun(_ => rt), u2)
  def vlam(x: String, fn: Val => Val): Val = VLam(bind(x), Expl, CFun(fn))
  def vlamI(x: String, fn: Val => Val): Val =
    VLam(bind(x), Impl(Unif), CFun(fn))
  def vlamlvl(x: String, body: VFinLevel => Val): Val =
    VLamLvl(bind(x), CFun(body))
  def vsigma(x: String, ty: Val, u1: VLevel, u2: VLevel, fn: Val => Val): Val =
    VSigma(bind(x), ty, u1, CFun(fn), u2)

  // matchers
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

  object VPrim:
    def apply(x: PrimName, sp: Spine = SId) = VRigid(HPrim(x), sp)
    def unapply(value: Val): Option[(PrimName, Spine)] = value match
      case VRigid(HPrim(x), spine) => Some((x, spine))
      case _                       => None

  object VLabel:
    def apply() = VRigid(HPrim(PLabel), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PLabel), SId) => true
      case _                          => false

  object VUnitType:
    def apply() = VRigid(HPrim(PUnitType), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnitType), SId) => true
      case _                             => false

  object VUnit:
    def apply() = VRigid(HPrim(PUnit), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnit), SId) => true
      case _                         => false

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

  object VLift:
    def apply(k: VFinLevel, l: VFinLevel, a: Val) =
      VRigid(HPrim(PLift), SApp(SAppLvl(SAppLvl(SId, k), l), a, Expl))
    def unapply(value: Val): Option[(VFinLevel, VFinLevel, Val)] = value match
      case VRigid(HPrim(PLift), SApp(SAppLvl(SAppLvl(SId, k), l), a, Expl)) =>
        Some((k, l, a))
      case _ => None

  object VLiftTerm:
    def apply(k: VFinLevel, l: VFinLevel, a: Val, t: Val) =
      VRigid(
        HPrim(PLiftTerm),
        SApp(SApp(SAppLvl(SAppLvl(SId, k), l), a, Impl(Unif)), t, Expl)
      )
    def unapply(value: Val): Option[(VFinLevel, VFinLevel, Val, Val)] =
      value match
        case VRigid(
              HPrim(PLiftTerm),
              SApp(SApp(SAppLvl(SAppLvl(SId, k), l), a, Impl(Unif)), t, Expl)
            ) =>
          Some((k, l, a, t))
        case _ => None

  object VId:
    def apply(l: VFinLevel, k: VFinLevel, a: Val, b: Val, x: Val, y: Val) =
      VRigid(
        HPrim(PId),
        SApp(
          SApp(
            SApp(
              SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)),
              b,
              Impl(Unif)
            ),
            x,
            Expl
          ),
          y,
          Expl
        )
      )
    def unapply(
        value: Val
    ): Option[(VFinLevel, VFinLevel, Val, Val, Val, Val)] = value match
      case VRigid(
            HPrim(PId),
            SApp(
              SApp(
                SApp(
                  SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)),
                  b,
                  Impl(Unif)
                ),
                x,
                Expl
              ),
              y,
              Expl
            )
          ) =>
        Some((l, k, a, b, x, y))
      case _ => None

  object VRefl:
    def apply(l: VFinLevel, a: Val, x: Val) =
      VRigid(
        HPrim(PRefl),
        SApp(
          SApp(SAppLvl(SId, l), a, Impl(Unif)),
          x,
          Expl
        )
      )
    def unapply(
        value: Val
    ): Option[(VFinLevel, Val, Val)] = value match
      case VRigid(
            HPrim(PRefl),
            SApp(
              SApp(SAppLvl(SId, l), a, Impl(Unif)),
              x,
              Expl
            )
          ) =>
        Some((l, a, x))
      case _ => None

  object VSing:
    def apply(l: VFinLevel, a: Val, x: Val) =
      VRigid(HPrim(PSing), SApp(SApp(SAppLvl(SId, l), a, Impl(Unif)), x, Expl))
    def unapply(value: Val): Option[(VFinLevel, Val, Val)] = value match
      case VRigid(
            HPrim(PSing),
            SApp(SApp(SAppLvl(SId, l), a, Impl(Unif)), x, Expl)
          ) =>
        Some((l, a, x))
      case _ => None

  object VSingCon:
    def apply(l: VFinLevel, a: Val, x: Val) =
      VRigid(
        HPrim(PSingCon),
        SApp(SApp(SAppLvl(SId, l), a, Impl(Unif)), x, Expl)
      )
    def unapply(value: Val): Option[(VFinLevel, Val, Val)] = value match
      case VRigid(
            HPrim(PSingCon),
            SApp(SApp(SAppLvl(SId, l), a, Impl(Unif)), x, Expl)
          ) =>
        Some((l, a, x))
      case _ => None

  object VNewtype:
    def apply(l: VFinLevel, k: VFinLevel, a: Val, b: Val, x: Val) =
      VRigid(
        HPrim(PNewtype),
        SApp(
          SApp(SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)), b, Expl),
          x,
          Expl
        )
      )
    def unapply(value: Val): Option[(VFinLevel, VFinLevel, Val, Val, Val)] =
      value match
        case VRigid(
              HPrim(PNewtype),
              SApp(
                SApp(SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)), b, Expl),
                x,
                Expl
              )
            ) =>
          Some((l, k, a, b, x))
        case _ => None

  object VPack:
    def apply(l: VFinLevel, k: VFinLevel, a: Val, b: Val, x: Val, t: Val) =
      VRigid(
        HPrim(PPack),
        SApp(
          SApp(
            SApp(
              SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)),
              b,
              Impl(Unif)
            ),
            x,
            Impl(Unif)
          ),
          t,
          Expl
        )
      )
    def unapply(
        value: Val
    ): Option[(VFinLevel, VFinLevel, Val, Val, Val, Val)] =
      value match
        case VRigid(
              HPrim(PPack),
              SApp(
                SApp(
                  SApp(
                    SApp(SAppLvl(SAppLvl(SId, l), k), a, Impl(Unif)),
                    b,
                    Impl(Unif)
                  ),
                  x,
                  Impl(Unif)
                ),
                t,
                Expl
              )
            ) =>
          Some((l, k, a, b, x, t))
        case _ => None
