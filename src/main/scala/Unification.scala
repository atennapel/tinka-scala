import Common.*
import Core.*
import Value.*
import Evaluation.*
import Errors.*

object Unification:
  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                 => ()
    case (SApp(a, v1), SApp(b, v2)) => unify(a, b); unify(v1, v2)
    case _                          => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit k: Lvl): Unit =
    val v = VVar(k)
    unify(a(v), b(v))(k + 1)

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit = (a, b) match
    case (VType, VType)                   => ()
    case (VPi(_, t1, b1), VPi(_, t2, b2)) => unify(t1, t2); unify(b1, b2)
    case (VLam(_, b1), VLam(_, b2))       => unify(b1, b2)
    case (VLam(_, b), w) => val v = VVar(k); unify(b(v), w(v))(k + 1)
    case (w, VLam(_, b)) => val v = VVar(k); unify(w(v), b(v))(k + 1)
    case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unify(sp1, sp2)
    case _ => throw UnifyError(s"${a.quote} ~ ${b.quote}")
