import Common.*
import Value.*
import Value.Val.*
import Value.Elim.*
import Errors.*
import Evaluation.*

object Unification:
  private def unifySp(l: Lvl, sp1: Spine, sp2: Spine): Unit = (sp1, sp2) match
    case (List(), List()) => ()
    case (EApp(v1) :: sp1, EApp(v2) :: sp2) =>
      unifySp(l, sp1, sp2)
      unify(l, v1, v2)
    case _ => throw UnifyError()

  def unify(l: Lvl, t: Val, u: Val): Unit = (t, u) match
    case (VType, VType) => ()
    case (VPi(x1, ty1, body1), VPi(x2, ty2, body2)) =>
      unify(l, ty1, ty2)
      val v = VVar(l)
      unify(lvlInc(l), vinst(body1, v), vinst(body2, v))

    case (VLam(_, body1), VLam(_, body2)) =>
      val v = VVar(l)
      unify(lvlInc(l), vinst(body1, v), vinst(body2, v))
    case (VLam(_, body), w) =>
      val v = VVar(l)
      unify(lvlInc(l), vinst(body, v), vapp(w, v))
    case (w, VLam(_, body)) =>
      val v = VVar(l)
      unify(lvlInc(l), vapp(w, v), vinst(body, v))

    case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unifySp(l, sp1, sp2)

    case (VGlobal(h1, sp1, v1), VGlobal(h2, sp2, v2)) if h1 == h2 =>
      try unifySp(l, sp1, sp2)
      catch case UnifyError() => unify(l, v1(), v2())
    case (VGlobal(_, _, v1), VGlobal(_, _, v2)) => unify(l, v1(), v2())
    case (VGlobal(_, _, v1), v2)                => unify(l, v1(), v2)
    case (v1, VGlobal(_, _, v2))                => unify(l, v1, v2())

    case _ => throw UnifyError()
