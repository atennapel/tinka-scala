import Common.*
import Value.*
import Evaluation.*
import Syntax.ProjType.*
import Errors.UnifyError

object Unification:
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

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit = (a, b) match
    case (VType, VType) => ()

    case (VPi(_, i1, t1, b1), VPi(_, i2, t2, b2)) if i1 == i2 =>
      unify(t1, t2); unify(b1, b2)
    case (VSigma(_, t1, b1), VSigma(_, t2, b2)) => unify(t1, t2); unify(b1, b2)

    case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
    case (VLam(_, i, b), v) =>
      val w = VVar(l); unify(b.inst(w), vapp(v, w, i))(l + 1)
    case (v, VLam(_, i, b)) =>
      val w = VVar(l); unify(vapp(v, w, i), b.inst(w))(l + 1)

    case (VPair(a1, b1), VPair(a2, b2)) => unify(a1, a2); unify(b1, b2)
    case (VPair(a, b), v) => unify(a, vproj(v, Fst)); unify(b, vproj(v, Snd))
    case (v, VPair(a, b)) => unify(vproj(v, Fst), a); unify(vproj(v, Snd), b)

    case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

    case _ => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
