import Common.*
import Core.*
import Value.*
import Evaluation.*
import Metas.*
import Errors.*
import Debug.*

import scala.collection.immutable.IntMap

object Unification:
  private final case class PRen(dom: Lvl, cod: Lvl, ren: IntMap[Lvl]):
    def lift: PRen = PRen(dom + 1, cod + 1, ren + (cod.expose, dom))

  private def invert(sp: Spine)(implicit gamma: Lvl): PRen =
    def go(sp: Spine): (Lvl, IntMap[Lvl]) = sp match
      case SId => (lvl0, IntMap.empty)
      case SApp(sp, t, _) =>
        val (dom, ren) = go(sp)
        t.force match
          case VVar(x) if !ren.contains(x.expose) =>
            (dom + 1, ren + (x.expose, dom))
          case VVar(_) => throw UnifyError("non-linear meta spine")
          case _       => throw UnifyError("non-var in meta spine")
      case _ => throw UnifyError("non-app in meta spine")
    val (dom, ren) = go(sp)
    PRen(dom, gamma, ren)

  private def rename(m: MetaId, v: Val)(implicit pren: PRen): Tm =
    def goSp(t: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => t
      case SApp(sp, a, i) => App(goSp(t, sp), go(a), i)
      case SProj(sp, p)   => Proj(goSp(t, sp), p)
    def go(v: Val)(implicit pren: PRen): Tm = v.force match
      case VNe(HVar(x), sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError("escaping variable")
          case Some(x2) => goSp(Var(x2.toIx(pren.dom)), sp)
      case VNe(HMeta(x), _) if m == x =>
        throw UnifyError(s"occurs check failed ?$x")
      case VNe(HMeta(x), sp) => goSp(Meta(x), sp)
      case VType             => Type
      case VUnitType         => UnitType
      case VUnit             => Unit
      case VPair(fst, snd)   => Pair(go(fst), go(snd))
      case VLam(bind, icit, body) =>
        Lam(bind, icit, go(body(VVar(pren.cod)))(pren.lift))
      case VPi(bind, icit, ty, body) =>
        Pi(bind, icit, go(ty), go(body(VVar(pren.cod)))(pren.lift))
      case VSigma(bind, ty, body) =>
        Sigma(bind, go(ty), go(body(VVar(pren.cod)))(pren.lift))
    go(v)

  private def icits(sp: Spine): List[Icit] = sp match
    case SId            => Nil
    case SApp(sp, _, i) => icits(sp) ++ List(i)
    case _              => throw Impossible

  private def lams(icits: List[Icit], body: Tm): Tm =
    def go(icits: List[Icit], ix: Int): Tm = icits match
      case Nil        => body
      case i :: icits => Lam(DoBind(Name(s"x$ix")), i, go(icits, ix + 1))
    go(icits, 0)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit gamma: Lvl): Unit =
    debug(s"solve ?$id := ${v.quote}")
    implicit val pren: PRen = invert(sp)
    val rhs = rename(id, v)
    val solution = lams(icits(sp), rhs)
    debug(s"solution ?$id := $solution")
    solveMeta(id, solution.eval(Nil))

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

      case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unify(sp1, sp2)

      case (VNe(HMeta(m), sp), v) => solve(m, sp, v)
      case (v, VNe(HMeta(m), sp)) => solve(m, sp, v)

      case (VUnit, _) => ()
      case (_, VUnit) => ()

      case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
