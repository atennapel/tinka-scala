import Common.*
import Core.*
import Surface as S
import Value.*
import Evaluation.*
import Unification.*
import Ctx.*
import Errors.*
import Debug.*

object Elaboration:
  private def unify(a: Val, b: Val)(implicit ctx: Ctx): Unit =
    try unifyCtx(a, b)
    catch
      case err: UnifyError =>
        throw ElabUnifyError(s"${a.quoteCtx} ~ ${b.quoteCtx}")

  private def checkType(ty: S.Ty)(implicit ctx: Ctx): Ty = check(ty, VType)

  private def checkOptionalType(tm: S.Tm, ty: Option[S.Ty])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) =
    ty match
      case Some(ty) =>
        val ety = checkType(ty)
        val vty = ety.evalCtx
        val etm = check(tm, vty)
        (etm, ety, vty)
      case None =>
        val (etm, vty) = infer(tm)
        (etm, vty.quoteCtx, vty)

  private def check(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm =
    debug(s"check $tm : ${ty.quoteCtx}")
    (tm, ty) match
      case (S.Type, VType)     => Type
      case (S.UnitType, VType) => UnitType
      case (S.Unit, VUnitType) => Unit
      case (S.Hole, VUnitType) => Unit
      case (S.Hole, _)         => throw HoleFoundError(ty.quoteCtx.toString)
      case (S.Lam(x, oty, b), VPi(y, pty, rty)) =>
        oty.foreach(ty => unify(checkType(ty).evalCtx, pty))
        val eb = check(b, rty.underCtx)(ctx.bind(x, pty))
        Lam(x, eb)
      case (S.Let(x, oty, v, b), _) =>
        val (ev, ety, vty) = checkOptionalType(v, oty)
        val eb = check(b, ty)(ctx.define(x, vty, ev.evalCtx))
        Let(x, ety, ev, eb)
      case _ =>
        val (etm, ty2) = infer(tm)
        unify(ty2, ty)
        etm

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy) =
    debug(s"infer $tm")
    tm match
      case S.Type     => (Type, VType)
      case S.UnitType => (UnitType, VType)
      case S.Unit     => (Unit, VUnitType)
      case S.Var(x) =>
        lookupCtx(x) match
          case Some((ix, vty)) => (Var(ix), vty)
          case None            => throw UndefinedVarError(x.toString)
      case S.Let(x, oty, v, b) =>
        val (ev, ety, vty) = checkOptionalType(v, oty)
        val (eb, rty) = infer(b)(ctx.define(x, vty, ev.evalCtx))
        (Let(x, ety, ev, eb), rty)
      case S.Pi(x, ty, b) =>
        val ety = checkType(ty)
        val eb = checkType(b)(ctx.bind(x, ety.evalCtx))
        (Pi(x, ety, eb), VType)
      case S.Sigma(x, ty, b) =>
        val ety = checkType(ty)
        val eb = checkType(b)(ctx.bind(x, ety.evalCtx))
        (Sigma(x, ety, eb), VType)
      case S.App(f, a) =>
        val (ef, fty) = infer(f)
        fty match
          case VPi(_, pty, rty) =>
            val ea = check(a, pty)
            (App(ef, ea), rty(ea.evalCtx))
          case _ => throw ExpectedPiError(s"in ${tm}, but got ${fty.quoteCtx}")
      case S.Lam(x, Some(ty), b) =>
        val vty = checkType(ty).evalCtx
        val (eb, rty) = infer(b)(ctx.bind(x, vty))
        (Lam(x, eb), VPi(x, vty, rty.closeCtx))
      case S.Lam(_, None, _) => throw CannotInferError(tm.toString)
      case S.Hole            => throw CannotInferError(tm.toString)

  def elaborate(tm: S.Tm): (Tm, Ty) =
    implicit val ctx = Ctx.empty
    val (etm, vty) = infer(tm)
    (etm, vty.quoteCtx)
