import Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Syntax.ProjType.*
import Metas.*
import Errors.UnifyError
import Debug.debug

import scala.collection.immutable.IntMap
import scala.util.Try

object Unification:
  private final case class PRen(
      occ: Option[MetaId],
      dom: Lvl,
      cod: Lvl,
      ren: IntMap[Lvl]
  ):
    def lift: PRen = PRen(occ, dom + 1, cod + 1, ren + (cod.expose, dom))
    def skip: PRen = PRen(occ, dom, cod + 1, ren)

  private def invert(sp: Spine)(implicit
      gamma: Lvl
  ): Either[MetaId, (PRen, Option[Pruning])] =
    def go(
        sp: Spine
    ): Either[MetaId, (Lvl, Set[Lvl], IntMap[Lvl], Pruning, Boolean)] =
      sp match
        case SId => Right((lvl0, Set.empty, IntMap.empty, Nil, true))
        case SApp(sp, t, i) =>
          go(sp).flatMap { (dom, domvars, ren, pr, isLinear) =>
            force(t) match
              case VVar(x) if domvars.contains(x) =>
                Right((dom + 1, domvars, ren - x.expose, None :: pr, false))
              case VVar(x) =>
                Right(
                  (
                    dom + 1,
                    domvars + x,
                    ren + (x.expose, dom),
                    Some(i) :: pr,
                    isLinear
                  )
                )
              case VFlex(m, _) => Left(m)
              case _           => throw UnifyError("non-var in meta spine")
          }
        case SAppLvl(sp, l) =>
          go(sp).flatMap { (dom, domvars, ren, pr, isLinear) =>
            force(l) match
              case VFinLevelVar(x, 0) if domvars.contains(x) =>
                Right((dom + 1, domvars, ren - x.expose, None :: pr, false))
              case VFinLevelVar(x, 0) =>
                Right(
                  (
                    dom + 1,
                    domvars + x,
                    ren + (x.expose, dom),
                    Some(Impl) :: pr,
                    isLinear
                  )
                )
              case _ => throw UnifyError("non-var in meta spine")
          }
        case _ => throw UnifyError("non-app in meta spine")
    go(sp).map { (dom, domvars, ren, pr, isLinear) =>
      (PRen(None, dom, gamma, ren), if isLinear then None else Some(pr))
    }

  private def pruneTy(pr: RevPruning, ty: VTy): Ty =
    def go(pr: Pruning, ty: VTy)(implicit pren: PRen): Ty =
      (pr, force(ty)) match
        case (Nil, ty) => rename(ty)
        case (Some(_) :: pr, VPi(x, i, a, u1, b, u2)) =>
          Pi(
            x,
            i,
            rename(a),
            rename(u1),
            go(pr, b.inst(VVar(pren.cod)))(pren.lift),
            rename(u2)
          )
        case (None :: pr, VPi(x, i, a, _, b, _)) =>
          go(pr, b.inst(VVar(pren.cod)))(pren.skip)
        case (Some(_) :: pr, VPiLvl(x, b, u)) =>
          val v = VFinLevel.vr(pren.cod)
          PiLvl(x, go(pr, b.inst(v))(pren.lift), rename(u.inst(v))(pren.lift))
        case _ => impossible()
    implicit val pren: PRen = PRen(None, lvl0, lvl0, IntMap.empty)
    go(pr.expose, ty)

  private def pruneMeta(pr: Pruning, m: MetaId): MetaId =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = eval(pruneTy(revPruning(pr), mty))(EEmpty)
    val m2 = freshMeta(prunedty)
    val solution = lams(mkLvl(pr.size), mty, AppPruning(Meta(m2), pr))
    solveMeta(m, eval(solution)(EEmpty), solution)
    m2

  private enum SpinePruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import SpinePruneStatus.*

  private def pruneFlex(m: MetaId, sp: Spine)(implicit pren: PRen): Tm =
    def spineToPruning(
        sp: List[(Option[Either[FinLevel, Tm]], Icit)]
    ): Pruning = sp match
      case Nil          => Nil
      case (t, i) :: sp => t.map(_ => i) :: spineToPruning(sp)
    def go(
        sp: Spine
    ): (List[(Option[Either[FinLevel, Tm]], Icit)], SpinePruneStatus) = sp match
      case SId => (Nil, OKRenaming)
      case SApp(sp, t, i) =>
        val (sp2, status) = go(sp)
        force(t) match
          case VVar(x) =>
            (pren.ren.get(x.expose), status) match
              case (Some(x), _) =>
                ((Some(Right(Var(x.toIx(pren.dom)))), i) :: sp2, status)
              case (None, OKNonRenaming) =>
                throw UnifyError("failed to prune")
              case _ => ((None, i) :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => throw UnifyError("failed to prune")
              case _ => ((Some(Right(rename(t))), i) :: sp2, OKNonRenaming)
      case SAppLvl(sp, t) =>
        val (sp2, status) = go(sp)
        force(t) match
          case VFinLevelVar(x, 0) =>
            (pren.ren.get(x.expose), status) match
              case (Some(x), _) =>
                ((Some(Left(LVar(x.toIx(pren.dom)))), Impl) :: sp2, status)
              case (None, OKNonRenaming) =>
                throw UnifyError("failed to prune")
              case _ => ((None, Impl) :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => throw UnifyError("failed to prune")
              case _ =>
                ((Some(Left(quote(t)(pren.dom))), Impl) :: sp2, OKNonRenaming)
      case _ => impossible()
    val (sp2, status) = go(sp)
    val m2 = status match
      case NeedsPruning => pruneMeta(spineToPruning(sp2), m)
      case _            => getMetaUnsolved(m); m
    sp2.foldRight(Meta(m2)) { case ((mu, i), t) =>
      mu.fold(t)(arg => arg.fold(AppLvl(t, _), App(t, _, i)))
    }

  private def rename(v: VFinLevel)(implicit pren: PRen): FinLevel =
    quote(v)(pren.dom)
  private def rename(v: VLevel)(implicit pren: PRen): Level = quote(v)(pren.dom)
  private def rename(v: Val)(implicit pren: PRen): Tm =
    def goSp(t: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => t
      case SApp(sp, a, i) => App(goSp(t, sp), go(a), i)
      case SAppLvl(sp, a) => AppLvl(goSp(t, sp), rename(a))
      case SProj(sp, p)   => Proj(goSp(t, sp), p)
    def go(v: Val)(implicit pren: PRen): Tm = force(v, UnfoldMetas) match
      case VUnitType  => UnitType
      case VUnitValue => UnitValue
      case VRigid(HVar(x), sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError("escaping variable")
          case Some(x2) => goSp(Var(x2.toIx(pren.dom)), sp)
      case VFlex(x, sp) =>
        pren.occ match
          case Some(y) if x == y => throw UnifyError(s"occurs check failed ?$x")
          case _                 => pruneFlex(x, sp)
      case VType(l)        => Type(rename(l))
      case VPair(fst, snd) => Pair(go(fst), go(snd))
      case VLam(bind, icit, body) =>
        Lam(bind, icit, go(body.inst(VVar(pren.cod)))(pren.lift))
      case VPi(bind, icit, ty, u1, body, u2) =>
        Pi(
          bind,
          icit,
          go(ty),
          rename(u1),
          go(body.inst(VVar(pren.cod)))(pren.lift),
          rename(u2)
        )
      case VPiLvl(x, body, u) =>
        val v = VFinLevel.vr(pren.cod)
        PiLvl(x, go(body.inst(v))(pren.lift), rename(u.inst(v))(pren.lift))
      case VLamLvl(x, body) =>
        LamLvl(x, go(body.inst(VFinLevel.vr(pren.cod)))(pren.lift))
      case VSigma(bind, ty, u1, body, u2) =>
        Sigma(
          bind,
          go(ty),
          rename(u1),
          go(body.inst(VVar(pren.cod)))(pren.lift),
          rename(u2)
        )
    go(v)

  private def lams(k: Lvl, ty: VTy, body: Tm): Tm =
    def go(ty: VTy, k2: Lvl): Tm =
      if k == k2 then body
      else
        force(ty) match
          case VPi(DontBind, i, _, _, b, _) =>
            Lam(DoBind(Name(s"x$k2")), i, go(b.inst(VVar(k2)), k2 + 1))
          case VPi(x @ DoBind(_), i, _, _, b, _) =>
            Lam(x, i, go(b.inst(VVar(k2)), k2 + 1))
          case VPiLvl(DontBind, b, _) =>
            LamLvl(DoBind(Name(s"l$k2")), go(b.inst(VFinLevel.vr(k2)), k2 + 1))
          case VPiLvl(x @ DoBind(_), b, _) =>
            LamLvl(x, go(b.inst(VFinLevel.vr(k2)), k2 + 1))
          case _ => impossible()
    go(ty, lvl0)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit l: Lvl): Unit =
    debug(s"solve ?$id := ${quote(v)}")
    invert(sp) match
      case Right(res) => solveWithPRen(id, res, v)
      case Left(m)    => throw UnifyError(s"invert blocked on ?$m")

  private def solveWithPRen(
      m: MetaId,
      res: (PRen, Option[Pruning]),
      v: Val
  ): Unit =
    val (pren, pruneNonLinear) = res
    val u = getMetaUnsolved(m)
    val mty = u.ty
    pruneNonLinear.foreach(pr => pruneTy(revPruning(pr), mty))
    val rhs = rename(v)(pren.copy(occ = Some(m)))
    val solution = lams(pren.dom, mty, rhs)
    debug(s"solution ?$m := $solution")
    solveMeta(m, eval(solution)(EEmpty), solution)

  private def intersect(m: MetaId, sp1: Spine, sp2: Spine)(implicit
      l: Lvl
  ): Unit =
    debug(s"intersect ?$m")
    def go(sp: Spine, sp2: Spine): Option[Pruning] = (sp, sp2) match
      case (SId, SId) => Some(Nil)
      case (SApp(sp, t, i), SApp(sp2, t2, _)) =>
        (force(t), force(t2)) match
          case (VVar(x), VVar(x2)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(i) else None) :: pr)
          case _ => None
      case (SAppLvl(sp, t), SAppLvl(sp2, t2)) =>
        (force(t), force(t2)) match
          case (VFinLevelVar(x, 0), VFinLevelVar(x2, 0)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(Impl) else None) :: pr)
          case _ => None
      case (SProj(_, _), SProj(_, _)) => None
      case _                          => impossible()
    go(sp1, sp2) match
      case None                             => unify(sp1, sp2)
      case Some(pr) if pr.exists(_.isEmpty) => pruneMeta(pr, m)
      case _                                => ()

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(implicit
      l: Lvl
  ): Unit =
    debug(s"flexFlex ?$m1 ~ ?$m2")
    def go(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine): Unit =
      Try(invert(sp)).toEither match
        case Right(Right(res))   => solveWithPRen(m, res, VFlex(m2, sp2))
        case Right(_)            => solve(m2, sp2, VFlex(m, sp))
        case Left(_: UnifyError) => solve(m2, sp2, VFlex(m, sp))
        case Left(err)           => throw err
    if sp1.size < sp2.size then go(m2, sp2, m1, sp1) else go(m1, sp1, m2, sp2)

  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError(s"spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit =
    (a, b) match
      case (SId, SId)                       => return ()
      case (SApp(s1, a, _), SApp(s2, b, _)) => unify(s1, s2); unify(a, b)
      case (SAppLvl(a, v1), SAppLvl(b, v2)) => unify(a, b); unify(v1, v2)
      case (SProj(s1, p1), SProj(s2, p2)) if p1 == p2 => unify(s1, s2)
      case (SProj(s1, Fst), SProj(s2, Named(_, n)))   => unifyProj(s1, s2, n)
      case (SProj(s1, Named(_, n)), SProj(s2, Fst))   => unifyProj(s2, s1, n)
      case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos[Val], b: Clos[Val])(implicit l: Lvl): Unit =
    val v = VVar(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  private def unifyClosLvl(a: Clos[VFinLevel], b: Clos[VFinLevel])(implicit
      l: Lvl
  ): Unit =
    val v = VFinLevel.vr(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  private def unify(a: ClosLvl, b: ClosLvl)(implicit k: Lvl): Unit =
    val v = VFinLevel.vr(k)
    unify(a.inst(v), b.inst(v))(k + 1)

  private def solveFinLevel(m: LMetaId, sp: List[VFinLevel], v: VFinLevel)(
      implicit k: Lvl
  ): Unit =
    debug(s"solve ?l$m (${sp.map(quote).mkString(", ")}) := ${quote(v)}")
    def toSpine(sp: List[VFinLevel]): Spine = sp match
      case l :: sp => SAppLvl(toSpine(sp), l)
      case Nil     => SId
    invert(toSpine(sp)) match
      case Left(id) => throw UnifyError(s"invert stuck on ?$id")
      case Right((_, Some(_))) =>
        throw UnifyError(s"need to prune in levels (unimplemented)")
      case Right((pren, _)) => ???

    /*
    if v.metas.contains(m.expose) then
      throw UnifyError(s"occurs check failed in ?l$m := ${quote(v)}")
    if v.vars.keys.map(mkLvl(_)).exists(k => !scope.contains(k)) then
      throw UnifyError(
        s"scope check failed in ?l$m ${
            if scope.nonEmpty then s"${scope.map(x => s"'$x").mkString(" ")} "
            else ""
          }:= ${quote(v)}"
      )
     */
    debug(s"solution ?l$m := ${quote(v)(k)}")
    solveLMeta(m, v)

  def unify(a: VFinLevel, b: VFinLevel)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a), force(b)) match
      case (a, b) if a == b             => ()
      case (VFinLevelMeta(m, 0, sp), b) => solveFinLevel(m, sp, b)
      case (b, VFinLevelMeta(m, 0, sp)) => solveFinLevel(m, sp, b)
      case (VFinLevelNat(0), VFinLevel(0, m1, m2)) if m1.isEmpty && m2.forall {
            case (_, (n, _)) => n == 0
          } =>
        m2.foreach { case (id, (_, sp)) =>
          unify(VFinLevelNat(0), VFinLevelMeta(lmetaId(id), 0, sp))
        }
      case (VFinLevel(0, m1, m2), VFinLevelNat(0)) if m1.isEmpty && m2.forall {
            case (_, (n, _)) => n == 0
          } =>
        m2.foreach { case (id, (_, sp)) =>
          unify(VFinLevelMeta(lmetaId(id), 0, sp), VFinLevelNat(0))
        }
      case (a, b) =>
        val m = (List(a.k) ++ a.vars.values ++ b.vars.values ++
          List(b.k) ++ a.metas.values.map(_._1) ++ b.metas.values.map(_._1)).min
        if m > 0 then
          debug(s"common factor $m")
          (a - m, b - m) match
            case (Some(as), Some(bs)) => unify(as, bs)
            case _ => throw UnifyError(s"${quote(a)} ~ ${quote(b)}")
        else throw UnifyError(s"${quote(a)} ~ ${quote(b)}")

  def unify(a: VLevel, b: VLevel)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (a, b) match
      case (VOmega1, VOmega1) => ()
      case (VOmega, VOmega)   => ()
      case (VFL(a), VFL(b))   => unify(a, b)
      case _ =>
        throw UnifyError(s"cannot unify levels ${quote(a)} ~ ${quote(b)}")

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VType(u1), VType(u2)) => unify(u1, u2)
      case (VUnitType, VUnitType) => ()

      case (VPi(_, i1, t1, u11, b1, u12), VPi(_, i2, t2, u21, b2, u22))
          if i1 == i2 =>
        unify(u11, u21); unify(u12, u22); unify(t1, t2); unify(b1, b2)
      case (VSigma(_, t1, u11, b1, u12), VSigma(_, t2, u21, b2, u22)) =>
        unify(u11, u21); unify(u12, u22); unify(t1, t2); unify(b1, b2)
      case (VPiLvl(_, b1, u1), VPiLvl(_, b2, u2)) =>
        unifyClosLvl(b1, b2); unify(u1, u2)

      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VLam(_, i, b), v) =>
        val w = VVar(l); unify(b.inst(w), vapp(v, w, i))(l + 1)
      case (v, VLam(_, i, b)) =>
        val w = VVar(l); unify(vapp(v, w, i), b.inst(w))(l + 1)

      case (VLamLvl(_, b1), VLamLvl(_, b2)) => unifyClosLvl(b1, b2)
      case (VLamLvl(_, b), w) =>
        val v = VFinLevel.vr(l); unify(b.inst(v), vapp(w, v))(l + 1)
      case (w, VLamLvl(_, b)) =>
        val v = VFinLevel.vr(l); unify(vapp(w, v), b.inst(v))(l + 1)

      case (VPair(a1, b1), VPair(a2, b2)) => unify(a1, a2); unify(b1, b2)
      case (VPair(a, b), v) => unify(a, vproj(v, Fst)); unify(b, vproj(v, Snd))
      case (v, VPair(a, b)) => unify(vproj(v, Fst), a); unify(vproj(v, Snd), b)

      case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

      case (VFlex(m1, sp1), VFlex(m2, sp2)) =>
        if m1 == m2 then intersect(m1, sp1, sp2)
        else flexFlex(m1, sp1, m2, sp2)
      case (VFlex(m, sp), v) => solve(m, sp, v)
      case (v, VFlex(m, sp)) => solve(m, sp, v)

      case (VUnitValue, _) => ()
      case (_, VUnitValue) => ()

      case _ => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
