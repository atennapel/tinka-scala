import Surface.{Tm as STm}
import Surface.Tm as S
import Surface.Decls
import Surface.Decl
import Surface.Decl.*
import Core.*
import Core.Tm.*
import Ctx.*
import Value.*
import Value.Val.*
import Evaluation.*
import Unification.*
import scala.util.parsing.input.{Position, NoPosition}
import Errors.*
import Globals.*
import Metas.*

object Elaboration:
  private def newMeta(ctx: Ctx): Tm = InsertedMeta(freshMeta(), ctx.bds)

  private def unifyCatch(ctx: Ctx, expected: Val, actual: Val): Unit =
    // println(s"unify: ${ctx.pretty(actual)} ~ ${ctx.pretty(expected)}")
    try unify(ctx.lvl, actual, expected)
    catch
      case e: UnifyError =>
        throw ElaborationUnifyError(
          s"${ctx.pretty(actual)} ~ ${ctx.pretty(expected)}: ${e.msg}\n${ctx.pos.longString}"
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
    // println(s"check: $tm : ${ctx.pretty(ty)}")
    (tm, force(ty)) match
      case (S.Hole, _) => newMeta(ctx)
      case (S.Lam(x, tyopt, body), VPi(_, pty, bty)) =>
        tyopt match
          case None =>
          case Some(ty) =>
            val vty = ctx.eval(checkType(ctx, tyopt.get))
            unifyCatch(ctx, pty, vty)
        Lam(x, check(ctx.bind(x, pty), body, vinst(bty, VVar(ctx.lvl))))
      case (S.Let(x, oty, value, body), _) =>
        val (ety, vty, evalue) = checkOptionalTy(ctx, oty, value)
        val vvalue = ctx.eval(evalue)
        Let(x, ety, evalue, check(ctx.define(x, vty, vvalue), body, ty))
      case (tm, _) =>
        val (etm, tyAct) = infer(ctx, tm)
        unifyCatch(ctx, ty, tyAct)
        etm

  private def checkType(ctx: Ctx, tm: STm): Tm = check(ctx, tm, VType)

  private def infer(ctx0: Ctx, tm: STm): (Tm, Val) =
    val ctx = ctx0.enter(tm.pos)
    // println(s"infer: $tm")
    tm match
      case S.Type => (Type, VType)
      case S.Var(name) =>
        ctx.lookup(name) match
          case Some((ix, ty)) => (Var(ix), ty)
          case None =>
            getGlobal(name) match
              case None     => throw VarError(s"$name\n${ctx.pos.longString}")
              case Some(ge) => (Global(name), ge.vty)
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
        val (ty, rty) = force(fty) match
          case VPi(x, ty, rty) => (ty, rty)
          case _ =>
            val ty = ctx.eval(newMeta(ctx))
            val rty = Clos(ctx.env, newMeta(ctx.bind("x", ty)))
            unifyCatch(ctx, VPi("x", ty, rty), fty)
            (ty, rty)
        val earg = check(ctx, arg, ty)
        (App(efn, earg), vinst(rty, ctx.eval(earg)))
      case S.Lam(x, tyopt, b) =>
        val va =
          ctx.eval(tyopt.map(ty => checkType(ctx, ty)).getOrElse(newMeta(ctx)))
        val (eb, vb) = infer(ctx.bind(x, va), b)
        (Lam(x, eb), VPi(x, va, ctx.closeVal(vb)))
      case S.Hole =>
        val a = ctx.eval(newMeta(ctx))
        val t = newMeta(ctx)
        (t, a)

  def elaborate(tm: STm, pos: Position = NoPosition): (Tm, Tm) =
    // TODO: reset metas and zonk
    // TODO: check for unsolved metas
    val ctx = Ctx.empty(pos)
    val (etm, vty) = infer(ctx, tm)
    (etm, ctx.quote(vty))

  def elaborateDecls(decls: Decls, pos: Position = NoPosition): Unit =
    decls.decls.foreach(elaborateDecl(_, pos))

  def elaborateDecl(decl: Decl, pos: Position = NoPosition): Unit = decl match
    case Def(x, v) =>
      if getGlobal(x).isDefined then throw GlobalError(x)
      val (etm, ety) = elaborate(v, pos)
      val vty = eval(List.empty, ety)
      val vval = eval(List.empty, etm)
      addGlobal(
        GlobalEntry(x, ety, vty, etm, vval, VGlobal(x, List.empty, () => vval))
      )
