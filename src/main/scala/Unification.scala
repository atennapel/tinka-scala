import Common.*
import Core.*
import Value.*
import Evaluation.*
import Metas.*
import Errors.*
import Debug.*

import scala.collection.immutable.IntMap
import scala.util.Try

class Unification(elab: IElaboration) extends IUnification:
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
            t.force match
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
              case VNe(HMeta(m), _) => Left(m)
              case _                => throw UnifyError("non-var in meta spine")
          }
        case SAppLvl(sp, l) =>
          go(sp).flatMap { (dom, domvars, ren, pr, isLinear) =>
            l.force match
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
      (PRen(None, dom, gamma, ren), if isLinear then Some(pr) else None)
    }

  private def pruneTy(pr: RevPruning, ty: VTy): Ty =
    def go(pr: Pruning, ty: VTy)(implicit pren: PRen): Ty = (pr, ty.force) match
      case (Nil, ty) => rename(ty)
      case (Some(_) :: pr, VPi(x, i, a, u1, b, u2)) =>
        Pi(
          x,
          i,
          rename(a),
          rename(u1),
          go(pr, b(VVar(pren.cod)))(pren.lift),
          rename(u2)
        )
      case (None :: pr, VPi(x, i, a, _, b, _)) =>
        go(pr, b(VVar(pren.cod)))(pren.skip)
      case (Some(_) :: pr, VPiLvl(x, b, u)) =>
        val v = VFinLevel.vr(pren.cod)
        PiLvl(x, go(pr, b(v))(pren.lift), rename(u(v))(pren.lift))
      case _ => throw Impossible
    implicit val pren: PRen = PRen(None, lvl0, lvl0, IntMap.empty)
    go(pr.expose, ty)

  private def pruneMeta(pr: Pruning, m: MetaId): MetaId =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = pruneTy(revPruning(pr), mty).eval(Nil)
    val m2 = freshMeta(u.blocking, prunedty)
    val solution = lams(mkLvl(pr.size), mty, AppPruning(Meta(m2), pr))
    solveMeta(m, solution.eval(Nil), solution)
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
        t.force match
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
        t.force match
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
                ((Some(Left(t.quote(pren.dom))), Impl) :: sp2, OKNonRenaming)
      case _ => throw Impossible
    val (sp2, status) = go(sp)
    val m2 = status match
      case NeedsPruning => pruneMeta(spineToPruning(sp2), m)
      case _            => getMetaUnsolved(m); m
    sp2.foldRight(Meta(m2)) { case ((mu, i), t) =>
      mu.fold(t)(arg => arg.fold(AppLvl(t, _), App(t, _, i)))
    }

  private def rename(v: VFinLevel)(implicit pren: PRen): FinLevel =
    v.quote(pren.dom)
  private def rename(v: VLevel)(implicit pren: PRen): Level = v.quote(pren.dom)
  private def rename(v: Val)(implicit pren: PRen): Tm =
    def goSp(t: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => t
      case SApp(sp, a, i) => App(goSp(t, sp), go(a), i)
      case SAppLvl(sp, a) => AppLvl(goSp(t, sp), rename(a))
      case SProj(sp, p)   => Proj(goSp(t, sp), p)
      case SPrim(sp, x, args) =>
        App(
          args.foldLeft(Prim(x))((fn, arg) =>
            arg.fold(
              lv => AppLvl(fn, rename(lv)),
              (a, i) => App(fn, go(a), i)
            )
          ),
          goSp(t, sp),
          Expl
        )
    def go(v: Val)(implicit pren: PRen): Tm = v.forceMetas match
      case VNe(HVar(x), sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError("escaping variable")
          case Some(x2) => goSp(Var(x2.toIx(pren.dom)), sp)
      case VNe(HMeta(x), sp) =>
        pren.occ match
          case Some(y) if x == y => throw UnifyError(s"occurs check failed ?$x")
          case _                 => pruneFlex(x, sp)
      case VNe(HPrim(x), sp)      => goSp(Prim(x), sp)
      case VGlobal(x, lvl, sp, _) => goSp(Global(x, lvl), sp)
      case VType(l)               => Type(rename(l))
      case VPair(fst, snd)        => Pair(go(fst), go(snd))
      case VLam(bind, icit, body) =>
        Lam(bind, icit, go(body(VVar(pren.cod)))(pren.lift))
      case VPi(bind, icit, ty, u1, body, u2) =>
        Pi(
          bind,
          icit,
          go(ty),
          rename(u1),
          go(body(VVar(pren.cod)))(pren.lift),
          rename(u2)
        )
      case VPiLvl(x, body, u) =>
        val v = VFinLevel.vr(pren.cod)
        PiLvl(x, go(body(v))(pren.lift), rename(u(v))(pren.lift))
      case VLamLvl(x, body) =>
        LamLvl(x, go(body(VFinLevel.vr(pren.cod)))(pren.lift))
      case VSigma(bind, ty, u1, body, u2) =>
        Sigma(
          bind,
          go(ty),
          rename(u1),
          go(body(VVar(pren.cod)))(pren.lift),
          rename(u2)
        )
    go(v)

  private def lams(k: Lvl, ty: VTy, body: Tm): Tm =
    def go(ty: VTy, k2: Lvl): Tm =
      if k == k2 then body
      else
        ty.force match
          case VPi(DontBind, i, _, _, b, _) =>
            Lam(DoBind(Name(s"x$k2")), i, go(b(VVar(k2)), k2 + 1))
          case VPi(x @ DoBind(_), i, _, _, b, _) =>
            Lam(x, i, go(b(VVar(k2)), k2 + 1))
          case VPiLvl(DontBind, b, _) =>
            LamLvl(DoBind(Name(s"l$k2")), go(b(VFinLevel.vr(k2)), k2 + 1))
          case VPiLvl(x @ DoBind(_), b, _) =>
            LamLvl(x, go(b(VFinLevel.vr(k2)), k2 + 1))
          case _ => throw Impossible
    go(ty, lvl0)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit gamma: Lvl): Unit =
    debug(s"solve ?$id := ${v.quote}")
    invert(sp) match
      case Right(res) => solveWithPRen(id, res, v)
      case Left(m) =>
        val pid = freshPostponedUnif(gamma, VNe(HMeta(id), sp), v)
        debug(s"postpone solve ?$id := ${v.quote} as !$pid blocked by ?$m")
        addBlocking(m, pid)

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
    solveMeta(m, solution.eval(Nil), solution)
    u.blocking.foreach(elab.retryPostpone)

  private def solveFinLevel(m: LMetaId, v: VFinLevel)(implicit k: Lvl): Unit =
    val LUnsolved(gamma, scope) = getLMetaUnsolved(m)
    debug(s"solve($k) ?l$m ($gamma) (${scope.mkString(", ")}) := ${v.quote}")
    if v.metas.contains(m.expose) then
      throw UnifyError(s"occurs check failed in ?l$m := ${v.quote}")
    if v.vars.keys.map(mkLvl(_)).exists(k => !scope.contains(k)) then
      throw UnifyError(
        s"scope check failed in ?l$m ${
            if scope.nonEmpty then s"${scope.map(x => s"'$x").mkString(" ")} "
            else ""
          }:= ${v.quote}"
      )
    debug(s"solution ?l$m := ${v.quote(gamma)}")
    solveLMeta(m, v)

  private def unify(a: VFinLevel, b: VFinLevel)(implicit k: Lvl): Unit =
    debug(s"unify fin level: ${a.quote} ~ ${b.quote}")
    (a.force, b.force) match
      case (a, b) if a == b         => return ()
      case (VFinLevelMeta(m, 0), b) => solveFinLevel(m, b)
      case (b, VFinLevelMeta(m, 0)) => solveFinLevel(m, b)
      case (VFinLevelMeta(m1, x), VFinLevelMeta(m2, y)) =>
        if x > y then unify(VFinLevelMeta(m1, x - y), VFinLevelMeta(m2, 0))
        else unify(VFinLevelMeta(m1, 0), VFinLevelMeta(m2, y - x))
      case (VFinLevelMeta(m, x), VFinLevelNat(y)) if y >= x =>
        unify(VFinLevelMeta(m, 0), VFinLevelNat(y - x))
      case (VFinLevelNat(y), VFinLevelMeta(m, x)) if y >= x =>
        unify(VFinLevelNat(y - x), VFinLevelMeta(m, 0))
      case (VFinLevelMeta(m, x), VFinLevelVar(l, y)) if y >= x =>
        unify(VFinLevelMeta(m, 0), VFinLevelVar(l, y - x))
      case (VFinLevelVar(l, y), VFinLevelMeta(m, x)) if y >= x =>
        unify(VFinLevelVar(l, y - x), VFinLevelMeta(m, 0))
      // TODO: more cases
      case (a @ VFinLevel(n1, xs1, ys1), b @ VFinLevel(n2, xs2, ys2)) =>
        val m = (List(n1) ++ xs1.values ++ ys1.values ++
          List(n2) ++ xs2.values ++ ys2.values).min
        if m > 0 then
          (a - m, b - m) match
            case (Some(as), Some(bs)) => unify(as, bs)
            case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
        else throw UnifyError(s"${a.quote} ~ ${b.quote}")

  override def unify(a: VLevel, b: VLevel)(implicit k: Lvl): Unit =
    debug(s"unify level: ${a.quote} ~ ${b.quote}")
    (a.force, b.force) match
      case (VOmega, VOmega)   => ()
      case (VOmega1, VOmega1) => ()
      case (VFL(a), VFL(b))   => unify(a, b)
      case (a, b)             => throw UnifyError(s"${a.quote} ~ ${b.quote}")

  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit k: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError("spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                               => ()
    case (SApp(a, v1, _), SApp(b, v2, _))         => unify(a, b); unify(v1, v2)
    case (SAppLvl(a, v1), SAppLvl(b, v2))         => unify(a, b); unify(v1, v2)
    case (SProj(a, p1), SProj(b, p2)) if p1 == p2 => unify(a, b)
    case (SProj(a, Fst), SProj(b, Named(_, n)))   => unifyProj(a, b, n)
    case (SProj(a, Named(_, n)), SProj(b, Fst))   => unifyProj(b, a, n)
    case (SPrim(a, x, args1), SPrim(b, y, args2)) if x == y =>
      unify(a, b)
      args1.zip(args2).foreach {
        case (Left(l), Left(k))             => unify(l, k)
        case (Right((v, _)), Right((w, _))) => unify(v, w)
        case _                              => throw Impossible
      }
    case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos[Val], b: Clos[Val])(implicit k: Lvl): Unit =
    val v = VVar(k)
    unify(a(v), b(v))(k + 1)

  private def unify(a: ClosLvl, b: ClosLvl)(implicit k: Lvl): Unit =
    val v = VFinLevel.vr(k)
    unify(a(v), b(v))(k + 1)

  private def unifyClosVFinLevel(a: Clos[VFinLevel], b: Clos[VFinLevel])(
      implicit k: Lvl
  ): Unit =
    val v = VFinLevel.vr(k)
    unify(a(v), b(v))(k + 1)

  private def flexFlex(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine)(implicit
      k: Lvl
  ): Unit =
    debug(s"flexFlex ?$m ~ ?$m2")
    def go(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine): Unit =
      Try(invert(sp)).toEither match
        case Right(Right(res))   => solveWithPRen(m, res, VNe(HMeta(m2), sp2))
        case Right(_)            => solve(m2, sp2, VNe(HMeta(m), sp))
        case Left(_: UnifyError) => solve(m2, sp2, VNe(HMeta(m), sp))
        case Left(err)           => throw err
    if sp.size < sp2.size then go(m2, sp2, m, sp) else go(m, sp, m2, sp2)

  private def intersect(m: MetaId, sp: Spine, sp2: Spine)(implicit
      k: Lvl
  ): Unit =
    debug(s"intersect ?$m")
    def go(sp: Spine, sp2: Spine): Option[Pruning] = (sp, sp2) match
      case (SId, SId) => Some(Nil)
      case (SApp(sp, t, i), SApp(sp2, t2, _)) =>
        (t.force, t2.force) match
          case (VVar(x), VVar(x2)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(i) else None) :: pr)
          case _ => None
      case (SAppLvl(sp, t), SAppLvl(sp2, t2)) =>
        (t.force, t2.force) match
          case (VFinLevelVar(x, 0), VFinLevelVar(x2, 0)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(Impl) else None) :: pr)
          case _ => None
      case (SProj(_, _), SProj(_, _)) => None
      case _                          => throw Impossible
    go(sp, sp2) match
      case None                             => unify(sp, sp2)
      case Some(pr) if pr.exists(_.isEmpty) => pruneMeta(pr, m)
      case _                                => ()

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit =
    debug(s"unify: ${a.quote} ~ ${b.quote}")
    (a.forceMetas, b.forceMetas) match
      case (VType(l1), VType(l2)) => unify(l1, l2)
      case (VPi(_, i1, t1, u11, b1, u21), VPi(_, i2, t2, u12, b2, u22))
          if i1 == i2 =>
        unify(u11, u12); unify(u12, u22); unify(t1, t2); unify(b1, b2)
      case (VPiLvl(_, b1, u1), VPiLvl(_, b2, u2)) =>
        unify(u1, u2)
        unifyClosVFinLevel(b1, b2)
      case (VSigma(_, t1, u11, b1, u21), VSigma(_, t2, u12, b2, u22)) =>
        unify(u11, u12); unify(u12, u22); unify(t1, t2); unify(b1, b2)

      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VLam(_, i, b), w) => val v = VVar(k); unify(b(v), w(v, i))(k + 1)
      case (w, VLam(_, i, b)) => val v = VVar(k); unify(w(v, i), b(v))(k + 1)

      case (VLamLvl(_, b1), VLamLvl(_, b2)) => unifyClosVFinLevel(b1, b2)
      case (VLamLvl(_, b), w) =>
        val v = VFinLevel.vr(k); unify(b(v), w(v))(k + 1)
      case (w, VLamLvl(_, b)) =>
        val v = VFinLevel.vr(k); unify(w(v), b(v))(k + 1)

      case (VPair(fst1, snd1), VPair(fst2, snd2)) =>
        unify(fst1, fst2); unify(snd1, snd2)
      case (VPair(fst, snd), v) =>
        unify(fst, v.proj(Fst)); unify(snd, v.proj(Snd))
      case (v, VPair(fst, snd)) =>
        unify(v.proj(Fst), fst); unify(v.proj(Snd), snd)

      case (VNe(HMeta(m), sp), VNe(HMeta(m2), sp2)) =>
        if m == m2 then intersect(m, sp, sp2)
        else flexFlex(m, sp, m2, sp2)

      case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unify(sp1, sp2)

      case (VNe(HMeta(m), sp), v) => solve(m, sp, v)
      case (v, VNe(HMeta(m), sp)) => solve(m, sp, v)

      case (VGlobal(_, lvl1, sp1, v1), VGlobal(_, lvl2, sp2, v2))
          if lvl1 == lvl2 =>
        try unify(sp1, sp2)
        catch case _: UnifyError => unify(v1(), v2())
      case (VGlobal(_, _, _, v), VGlobal(_, _, _, w)) => unify(v(), w())
      case (VGlobal(_, _, _, v), w)                   => unify(v(), w)
      case (w, VGlobal(_, _, _, v))                   => unify(w, v())

      case (VUnit(), _) => ()
      case (_, VUnit()) => ()

      case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
