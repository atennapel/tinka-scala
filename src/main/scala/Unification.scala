import Common.*
import Value.*
import Evaluation.*
import Errors.UnifyError

object Unification:
  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit = (a, b) match
    case (SId, SId)                 => return ()
    case (SApp(s1, a), SApp(s2, b)) => unify(s1, s2); unify(a, b)
    case _                          => impossible()

  private def unify(a: Clos, b: Clos)(implicit l: Lvl): Unit =
    val v = VVar(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit = (a, b) match
    case (VType, VType) => ()

    case (VPi(_, t1, b1), VPi(_, t2, b2)) => unify(t1, t2); unify(b1, b2)

    case (VLam(_, b1), VLam(_, b2)) => unify(b1, b2)
    case (VLam(_, b), v) => val w = VVar(l); unify(b.inst(w), vapp(v, w))(l + 1)
    case (v, VLam(_, b)) => val w = VVar(l); unify(vapp(v, w), b.inst(w))(l + 1)

    case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

    case _ => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
