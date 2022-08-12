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

  private def invert(sp: Spine)(implicit gamma: Lvl): (PRen, Option[Pruning]) =
    def go(sp: Spine): (Lvl, Set[Lvl], IntMap[Lvl], Pruning, Boolean) = sp match
      case SId => (lvl0, Set.empty, IntMap.empty, Nil, true)
      case SApp(sp, t, i) =>
        val (dom, domvars, ren, pr, isLinear) = go(sp)
        t.force match
          case VVar(x) if domvars.contains(x) =>
            (dom + 1, domvars, ren - x.expose, None :: pr, false)
          case VVar(x) =>
            (
              dom + 1,
              domvars + x,
              ren + (x.expose, dom),
              Some(i) :: pr,
              isLinear
            )
          case _ => throw UnifyError("non-var in meta spine")
      case _ => throw UnifyError("non-app in meta spine")
    val (dom, domvars, ren, pr, isLinear) = go(sp)
    (PRen(None, dom, gamma, ren), if isLinear then Some(pr) else None)

  private def pruneTy(pr: RevPruning, ty: VTy): Ty =
    def go(pr: Pruning, ty: VTy)(implicit pren: PRen): Ty = (pr, ty.force) match
      case (Nil, ty) => rename(ty)
      case (Some(_) :: pr, VPi(x, i, a, b)) =>
        Pi(x, i, rename(a), go(pr, b(VVar(pren.cod)))(pren.lift))
      case (None :: pr, VPi(x, i, a, b)) =>
        go(pr, b(VVar(pren.cod)))(pren.skip)
      case _ => throw Impossible
    implicit val pren: PRen = PRen(None, lvl0, lvl0, IntMap.empty)
    go(pr.expose, ty)

  private def pruneMeta(pr: Pruning, m: MetaId): MetaId =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = pruneTy(revPruning(pr), mty).eval(Nil)
    val m2 = freshMeta(u.blocking, prunedty)
    val solution = lams(mkLvl(pr.size), mty, AppPruning(Meta(m2), pr)).eval(Nil)
    solveMeta(m, solution)
    m2

  private enum SpinePruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import SpinePruneStatus.*

  private def pruneFlex(m: MetaId, sp: Spine)(implicit pren: PRen): Tm =
    def spineToPruning(sp: List[(Option[Tm], Icit)]): Pruning = sp match
      case Nil          => Nil
      case (t, i) :: sp => t.map(_ => i) :: spineToPruning(sp)
    def go(sp: Spine): (List[(Option[Tm], Icit)], SpinePruneStatus) = sp match
      case SId => (Nil, OKRenaming)
      case SApp(sp, t, i) =>
        val (sp2, status) = go(sp)
        t.force match
          case VVar(x) =>
            (pren.ren.get(x.expose), status) match
              case (Some(x), _) =>
                ((Some(Var(x.toIx(pren.dom))), i) :: sp2, status)
              case (None, OKNonRenaming) =>
                throw UnifyError("failed to prune")
              case _ => ((None, i) :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => throw UnifyError("failed to prune")
              case _            => ((Some(rename(t)), i) :: sp2, OKNonRenaming)
      case _ => throw Impossible
    val (sp2, status) = go(sp)
    val m2 = status match
      case NeedsPruning => pruneMeta(spineToPruning(sp2), m)
      case _            => getMetaUnsolved(m); m
    sp2.foldRight(Meta(m2)) { case ((mu, i), t) => mu.fold(t)(App(t, _, i)) }

  private def rename(v: Val)(implicit pren: PRen): Tm =
    def goSp(t: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => t
      case SApp(sp, a, i) => App(goSp(t, sp), go(a), i)
      case SProj(sp, p)   => Proj(goSp(t, sp), p)
    def go(v: Val)(implicit pren: PRen): Tm = v.force match
      case VNe(HVar(x), sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError("escaping variable")
          case Some(x2) => goSp(Var(x2.toIx(pren.dom)), sp)
      case VNe(HMeta(x), sp) =>
        pren.occ match
          case Some(y) if x == y => throw UnifyError(s"occurs check failed ?$x")
          case _                 => pruneFlex(x, sp)
      case VType           => Type
      case VUnitType       => UnitType
      case VUnit           => Unit
      case VPair(fst, snd) => Pair(go(fst), go(snd))
      case VLam(bind, icit, body) =>
        Lam(bind, icit, go(body(VVar(pren.cod)))(pren.lift))
      case VPi(bind, icit, ty, body) =>
        Pi(bind, icit, go(ty), go(body(VVar(pren.cod)))(pren.lift))
      case VSigma(bind, ty, body) =>
        Sigma(bind, go(ty), go(body(VVar(pren.cod)))(pren.lift))
    go(v)

  private def lams(k: Lvl, ty: VTy, body: Tm): Tm =
    def go(ty: VTy, k2: Lvl): Tm =
      if k == k2 then body
      else
        ty.force match
          case VPi(DontBind, i, _, b) =>
            Lam(DoBind(Name(s"x$k2")), i, go(b(VVar(k2)), k2 + 1))
          case VPi(x @ DoBind(_), i, _, b) => Lam(x, i, go(b(VVar(k2)), k2 + 1))
          case _                           => throw Impossible
    go(ty, lvl0)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit gamma: Lvl): Unit =
    debug(s"solve ?$id := ${v.quote}")
    val res = invert(sp)
    solveWithPRen(id, res, v)

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
    solveMeta(m, solution.eval(Nil))
    u.blocking.foreach(elab.retryCheck)

  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit k: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError("spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                               => ()
    case (SApp(a, v1, _), SApp(b, v2, _))         => unify(a, b); unify(v1, v2)
    case (SProj(a, p1), SProj(b, p2)) if p1 == p2 => unify(a, b)
    case (SProj(a, Fst), SProj(b, Named(_, n)))   => unifyProj(a, b, n)
    case (SProj(a, Named(_, n)), SProj(b, Fst))   => unifyProj(b, a, n)
    case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit k: Lvl): Unit =
    val v = VVar(k)
    unify(a(v), b(v))(k + 1)

  private def flexFlex(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine)(implicit
      k: Lvl
  ): Unit =
    debug(s"flexFlex ?$m ~ ?$m2")
    def go(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine): Unit =
      Try(invert(sp)).toEither match
        case Right(res)          => solveWithPRen(m, res, VNe(HMeta(m2), sp2))
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
      case (SProj(_, _), SProj(_, _)) => None
      case _                          => throw Impossible
    go(sp, sp2) match
      case None                             => unify(sp, sp2)
      case Some(pr) if pr.exists(_.isEmpty) => pruneMeta(pr, m)
      case _                                => ()

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit =
    debug(s"unify ${a.quote} ~ ${b.quote}")
    (a.force, b.force) match
      case (VType, VType)         => ()
      case (VUnitType, VUnitType) => ()
      case (VPi(_, i1, t1, b1), VPi(_, i2, t2, b2)) if i1 == i2 =>
        unify(t1, t2); unify(b1, b2)
      case (VSigma(_, t1, b1), VSigma(_, t2, b2)) =>
        unify(t1, t2); unify(b1, b2)

      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VLam(_, i, b), w) => val v = VVar(k); unify(b(v), w(v, i))(k + 1)
      case (w, VLam(_, i, b)) => val v = VVar(k); unify(w(v, i), b(v))(k + 1)

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

      case (VUnit, _) => ()
      case (_, VUnit) => ()

      case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
