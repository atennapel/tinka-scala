import Common.*
import Presyntax.*
import Syntax.*
import Value.*
import Evaluation.*
import Unification.{unify as unify0}
import Errors.*

object Elaboration:
  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    try unify0(a, b)(ctx.lvl)
    catch
      case e: UnifyError =>
        throw ElabUnifyError(
          s"failed to unify ${ctx.quote(a)} ~ ${ctx.quote(b)}: ${e.msg}"
        )

  private def checkType(ty: RTm)(implicit ctx: Ctx): Ty = check(ty, VType)

  private def checkValue(tm: RTm, ty: Option[RTm])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) = ty match
    case Some(ty) =>
      val ety = checkType(ty)
      val vty = ctx.eval(ety)
      val etm = check(tm, vty)
      (etm, ety, vty)
    case None =>
      val (etm, vty) = infer(tm)
      (etm, ctx.quote(vty), vty)

  private def check(tm: RTm, ty: VTy)(implicit ctx: Ctx): Tm = (tm, ty) match
    case (RPos(pos, tm), _) => check(tm, ty)(ctx.enter(pos))
    case (RLam(x, _, ot, b), VPi(_, t, rt)) =>
      ot.foreach(t0 => unify(ctx.eval(checkType(t0)), t))
      val eb = check(b, ctx.inst(rt))(ctx.bind(x, t))
      Lam(x, eb)
    case (RLet(x, t, v, b), _) =>
      val (ev, et, vt) = checkValue(v, t)
      val eb = check(b, ty)(ctx.define(x, vt, ctx.eval(ev)))
      Let(x, et, ev, eb)
    case _ =>
      val (etm, vty) = infer(tm)
      unify(vty, ty)
      etm

  private def infer(tm: RTm)(implicit ctx: Ctx): (Tm, VTy) = tm match
    case RPos(pos, tm) => infer(tm)(ctx.enter(pos))
    case RType         => (Type, VType)
    case RVar(x) =>
      ctx.lookup(x) match
        case Some((ix, ty)) => (Var(ix), ty)
        case None           => throw UndefVarError(x.toString)
    case RLet(x, t, v, b) =>
      val (ev, et, vt) = checkValue(v, t)
      val (eb, rt) = infer(b)(ctx.define(x, vt, ctx.eval(ev)))
      (Let(x, et, ev, eb), rt)
    case RPi(x, _, t, b) =>
      val et = checkType(t)
      val eb = checkType(b)(ctx.bind(x, ctx.eval(et)))
      (Pi(x, et, eb), VType)
    case RApp(f, a, _) =>
      val (ef, ft) = infer(f)
      ft match
        case VPi(_, vt, b) =>
          val ea = check(a, vt)
          (App(ef, ea), b.inst(ctx.eval(ea)))
        case _ => throw NotPiError(tm.toString)
    case RLam(x, _, Some(t), b) =>
      val et = checkType(t)
      val vt = ctx.eval(et)
      val (eb, rt) = infer(b)(ctx.bind(x, vt))
      (Lam(x, eb), VPi(x, vt, ctx.close(rt)))
    case _ => throw CannotInferError(tm.toString)

  def elaborate(tm: RTm)(implicit ctx: Ctx = Ctx.empty()): (Tm, Ty) =
    val (etm, vty) = infer(tm)
    (etm, ctx.quote(vty))
