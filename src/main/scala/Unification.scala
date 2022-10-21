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
  ): (PRen, Option[Pruning]) =
    def go(
        sp: Spine
    ): (Lvl, Set[Lvl], IntMap[Lvl], Pruning, Boolean) =
      sp match
        case SId => (lvl0, Set.empty, IntMap.empty, Nil, true)
        case SApp(sp, t, i) =>
          val (dom, domvars, ren, pr, isLinear) = go(sp)
          force(t) match
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
    def go(pr: Pruning, ty: VTy)(implicit pren: PRen): Ty =
      (pr, force(ty)) match
        case (Nil, ty) => rename(ty)
        case (Some(_) :: pr, VPi(x, i, a, b)) =>
          Pi(
            x,
            i,
            rename(a),
            go(pr, b.inst(VVar(pren.cod)))(pren.lift)
          )
        case (None :: pr, VPi(x, i, a, b)) =>
          go(pr, b.inst(VVar(pren.cod)))(pren.skip)
        case _ => impossible()
    implicit val pren: PRen = PRen(None, lvl0, lvl0, IntMap.empty)
    go(pr.expose, ty)

  private def pruneMeta(pr: Pruning, m: MetaId): MetaId =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = eval(pruneTy(revPruning(pr), mty))(Nil)
    val m2 = freshMeta(u.blocking, prunedty)
    val solution = lams(mkLvl(pr.size), mty, AppPruning(Meta(m2), pr))
    solveMeta(m, eval(solution)(Nil), solution)
    m2

  private enum SpinePruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import SpinePruneStatus.*

  private def pruneFlex(m: MetaId, sp: Spine)(implicit pren: PRen): Tm =
    def spineToPruning(
        sp: List[(Option[Tm], Icit)]
    ): Pruning = sp match
      case Nil          => Nil
      case (t, i) :: sp => t.map(_ => i) :: spineToPruning(sp)
    def go(
        sp: Spine
    ): (List[(Option[Tm], Icit)], SpinePruneStatus) = sp match
      case SId => (Nil, OKRenaming)
      case SApp(sp, t, i) =>
        val (sp2, status) = go(sp)
        force(t) match
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
      case _ => impossible()
    val (sp2, status) = go(sp)
    val m2 = status match
      case NeedsPruning => pruneMeta(spineToPruning(sp2), m)
      case _            => getMetaUnsolved(m); m
    sp2.foldRight(Meta(m2)) { case ((mu, i), t) =>
      mu.fold(t)(App(t, _, i))
    }

  private def rename(v: Val)(implicit pren: PRen): Tm =
    def goSp(t: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => t
      case SApp(sp, a, i) => App(goSp(t, sp), go(a), i)
      case SProj(sp, p)   => Proj(goSp(t, sp), p)
    def go(v: Val)(implicit pren: PRen): Tm = force(v, UnfoldMetas) match
      case VRigid(x, sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError("escaping variable")
          case Some(x2) => goSp(Var(x2.toIx(pren.dom)), sp)
      case VFlex(x, sp) =>
        pren.occ match
          case Some(y) if x == y => throw UnifyError(s"occurs check failed ?$x")
          case _                 => pruneFlex(x, sp)
      case VUri(x, sp, _)  => goSp(Uri(x), sp)
      case VType           => Type
      case VUnitType       => UnitType
      case VUnitValue      => UnitValue
      case VPair(fst, snd) => Pair(go(fst), go(snd))
      case VLam(bind, icit, body) =>
        Lam(bind, icit, go(body.inst(VVar(pren.cod)))(pren.lift))
      case VPi(bind, icit, ty, body) =>
        Pi(
          bind,
          icit,
          go(ty),
          go(body.inst(VVar(pren.cod)))(pren.lift)
        )
      case VSigma(bind, ty, body) =>
        Sigma(
          bind,
          go(ty),
          go(body.inst(VVar(pren.cod)))(pren.lift)
        )
    go(v)

  private def lams(k: Lvl, ty: VTy, body: Tm): Tm =
    def go(ty: VTy, k2: Lvl): Tm =
      if k == k2 then body
      else
        force(ty) match
          case VPi(DontBind, i, _, b) =>
            Lam(DoBind(Name(s"x$k2")), i, go(b.inst(VVar(k2)), k2 + 1))
          case VPi(x @ DoBind(_), i, _, b) =>
            Lam(x, i, go(b.inst(VVar(k2)), k2 + 1))
          case _ => impossible()
    go(ty, lvl0)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit gamma: Lvl): Unit =
    debug(s"solve ?$id := ${quote(v)}")
    val pren = invert(sp)
    solveWithPRen(id, pren, v)

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
    solveMeta(m, eval(solution)(Nil), solution)
    u.blocking.foreach(elab.retryCheck)

  private def flexFlex(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine)(implicit
      k: Lvl
  ): Unit =
    debug(s"flexFlex ?$m ~ ?$m2")
    def go(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine): Unit =
      Try(invert(sp)).toEither match
        case Right(res)          => solveWithPRen(m, res, VFlex(m2, sp2))
        case Left(_: UnifyError) => solve(m2, sp2, VFlex(m, sp))
        case Left(err)           => throw err
    if sp.size < sp2.size then go(m2, sp2, m, sp) else go(m, sp, m2, sp2)

  private def intersect(m: MetaId, sp: Spine, sp2: Spine)(implicit
      k: Lvl
  ): Unit =
    debug(s"intersect ?$m")
    def go(sp: Spine, sp2: Spine): Option[Pruning] = (sp, sp2) match
      case (SId, SId) => Some(Nil)
      case (SApp(sp, t, i), SApp(sp2, t2, _)) =>
        (force(t), force(t2)) match
          case (VVar(x), VVar(x2)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(i) else None) :: pr)
          case _ => None
      case (SProj(_, _), SProj(_, _)) => None
      case _                          => impossible()
    go(sp, sp2) match
      case None                             => unify(sp, sp2)
      case Some(pr) if pr.exists(_.isEmpty) => pruneMeta(pr, m)
      case _                                => ()

  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError(s"spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit = (a, b) match
    case (SId, SId)                       => return ()
    case (SApp(s1, a, _), SApp(s2, b, _)) => unify(s1, s2); unify(a, b)
    case (SProj(s1, p1), SProj(s2, p2)) if p1 == p2 => unify(s1, s2)
    case (SProj(s1, Fst), SProj(s2, Named(_, n)))   => unifyProj(s1, s2, n)
    case (SProj(s1, Named(_, n)), SProj(s2, Fst))   => unifyProj(s1, s2, n)
    case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit l: Lvl): Unit =
    val v = VVar(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  override def unify(a: Val, b: Val)(implicit l: Lvl): Unit =
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VType, VType)           => ()
      case (VUnitType, VUnitType)   => ()
      case (VUnitValue, VUnitValue) => ()

      case (VPi(_, i1, t1, b1), VPi(_, i2, t2, b2)) if i1 == i2 =>
        unify(t1, t2); unify(b1, b2)
      case (VSigma(_, t1, b1), VSigma(_, t2, b2)) =>
        unify(t1, t2); unify(b1, b2)

      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VLam(_, i, b), v) =>
        val w = VVar(l); unify(b.inst(w), vapp(v, w, i))(l + 1)
      case (v, VLam(_, i, b)) =>
        val w = VVar(l); unify(vapp(v, w, i), b.inst(w))(l + 1)

      case (VPair(a1, b1), VPair(a2, b2)) => unify(a1, a2); unify(b1, b2)
      case (VPair(a, b), v) => unify(a, vproj(v, Fst)); unify(b, vproj(v, Snd))
      case (v, VPair(a, b)) => unify(vproj(v, Fst), a); unify(vproj(v, Snd), b)

      case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

      case (VFlex(m1, sp1), VFlex(m2, sp2)) =>
        if m1 == m2 then intersect(m1, sp1, sp2)
        else flexFlex(m1, sp1, m2, sp2)
      case (VFlex(m, sp), v) => solve(m, sp, v)
      case (v, VFlex(m, sp)) => solve(m, sp, v)

      case (VUri(uri1, sp1, v1), VUri(uri2, sp2, v2)) if uri1 == uri2 =>
        try unify(sp1, sp2)
        catch case _: UnifyError => unify(v1(), v2())
      case (VUri(_, _, v), VUri(_, _, w)) => unify(v(), w())
      case (VUri(_, _, v), w)             => unify(v(), w)
      case (w, VUri(_, _, v))             => unify(w, v())

      case (VUnitValue, _) => ()
      case (_, VUnitValue) => ()

      case _ => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
