import Surface.{Tm as STm}
import Surface.Tm as S
import Core.*
import Core.Tm.*
import Ctx.*
import Value.*
import Value.Val.*
import Evaluation.*
import Unification.*
import scala.util.parsing.input.{Position, NoPosition}
import Errors.*

object Elaboration:
  private def unifyCatch(ctx: Ctx, expected: Val, actual: Val): Unit =
    try unify(ctx.lvl, actual, expected)
    catch
      case e: UnifyError =>
        throw ElaborationUnifyError(
          s"${ctx.pretty(actual)} ~ ${ctx.pretty(expected)}\n${ctx.pos.longString}"
        )

  private def checkOptionalTy(
      ctx: Ctx,
      ty: Option[STm],
      value: STm
  ): (Tm, Val, Tm) =
    ty match
      case Some(sty) =>
        val ety = checkType(ctx, sty)
        val vty = ctx.eval(ety)
        (ety, vty, check(ctx, value, vty))
      case None =>
        val (evalue, vty) = infer(ctx, value)
        (ctx.quote(vty), vty, evalue)

  private def check(ctx0: Ctx, tm: STm, ty: Val): Tm =
    val ctx = ctx0.enter(tm.pos)
    (tm, ty) match
      case (S.Lam(x, body), VPi(_, pty, bty)) =>
        Lam(x, check(ctx.bind(x, pty), body, vinst(bty, VVar(ctx.lvl))))
      case (S.Let(x, oty, value, body), ty) =>
        val (ety, vty, evalue) = checkOptionalTy(ctx, oty, value)
        val vvalue = ctx.eval(evalue)
        Let(x, ety, evalue, check(ctx.define(x, vty, vvalue), body, ty))
      case (tm, tyEx) =>
        val (etm, tyAct) = infer(ctx, tm)
        unifyCatch(ctx, tyEx, tyAct)
        etm

  private def checkType(ctx: Ctx, tm: STm): Tm = check(ctx, tm, VType)

  private def infer(ctx0: Ctx, tm: STm): (Tm, Val) =
    val ctx = ctx0.enter(tm.pos)
    tm match
      case S.Type => (Type, VType)
      case S.Var(name) =>
        ctx.lookup(name) match
          case None           => throw VarError(s"$name\n${ctx.pos.longString}")
          case Some((ix, ty)) => (Var(ix), ty)
      case S.Let(x, oty, value, body) =>
        val (ety, vty, evalue) = checkOptionalTy(ctx, oty, value)
        val vvalue = ctx.eval(evalue)
        val (ebody, vbodyty) = infer(ctx.define(x, vty, vvalue), body)
        (Let(x, ety, evalue, ebody), vbodyty)
      case S.Pi(x, ty, body) =>
        val ety = checkType(ctx, ty)
        val ebody = checkType(ctx.bind(x, ctx.eval(ety)), body)
        (Pi(x, ety, ebody), VType)
      case app @ S.App(fn, arg) =>
        val (efn, fty) = infer(ctx, fn)
        fty match
          case VPi(x, ty, rty) =>
            val earg = check(ctx, arg, ty)
            (App(efn, earg), vinst(rty, ctx.eval(earg)))
          case ty =>
            throw NotPiError(
              s"$app, got ${ctx.pretty(ty)}\n${ctx.pos.longString}"
            )
      case S.Lam(_, _) => throw CannotInferError(s"$tm\n${ctx.pos.longString}")

  def elaborate(tm: STm, pos: Position = NoPosition): (Tm, Tm) =
    val ctx = Ctx.empty(pos)
    val (etm, vty) = infer(ctx, tm)
    (etm, ctx.quote(vty))
