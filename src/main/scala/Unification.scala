import Common.*
import Core.*
import Value.*
import Evaluation.*
import Errors.*

object Unification:
  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                               => ()
    case (SApp(a, v1, _), SApp(b, v2, _))         => unify(a, b); unify(v1, v2)
    case (SProj(a, p1), SProj(b, p2)) if p1 == p2 => unify(a, b)
    case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit k: Lvl): Unit =
    val v = VVar(k)
    unify(a(v), b(v))(k + 1)

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit = (a, b) match
    case (VType, VType)         => ()
    case (VUnitType, VUnitType) => ()
    case (VPi(_, i1, t1, b1), VPi(_, i2, t2, b2)) if i1 == i2 =>
      unify(t1, t2); unify(b1, b2)
    case (VSigma(_, t1, b1), VSigma(_, t2, b2)) => unify(t1, t2); unify(b1, b2)

    case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
    case (VLam(_, i, b), w) => val v = VVar(k); unify(b(v), w(v, i))(k + 1)
    case (w, VLam(_, i, b)) => val v = VVar(k); unify(w(v, i), b(v))(k + 1)

    case (VPair(fst1, snd1), VPair(fst2, snd2)) =>
      unify(fst1, fst2); unify(snd1, snd2)
    case (VPair(fst, snd), v) =>
      unify(fst, v.proj(Fst)); unify(snd, v.proj(Snd))
    case (v, VPair(fst, snd)) =>
      unify(v.proj(Fst), fst); unify(v.proj(Snd), snd)

    case (VUnit, _) => ()
    case (_, VUnit) => ()

    case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unify(sp1, sp2)
    case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
