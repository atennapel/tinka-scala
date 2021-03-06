import Surface.{Tm as STm}
import Surface.Tm as S
import Surface.ProjType as SP
import Surface.Decls
import Surface.Decl
import Surface.Decl.*
import Core.*
import Core.Tm.*
import Core.ProjType.*
import Ctx.*
import Value.*
import Value.Val.*
import Value.Clos.*
import Evaluation.*
import Unification.*
import Errors.*
import Globals.*
import Metas.*
import Common.*
import Common.Icit.*
import Debug.debug
import Primitives.*
import scala.util.parsing.input.{Position, NoPosition}
import scala.annotation.tailrec

object Elaboration:
  private def newMeta(ctx: Ctx): Tm = InsertedMeta(freshMeta(), ctx.bds)

  private def insertPi(ctx: Ctx, inp: (Tm, Val)): (Tm, Val) =
    val (tm, ty) = inp
    force(ty) match
      case VPi(x, Impl, a, b) =>
        val m = newMeta(ctx)
        val mv = ctx.eval(m)
        insertPi(ctx, (App(tm, m, Impl), vinst(b, mv)))
      case _ => (tm, ty)

  private def insert(ctx: Ctx, inp: (Tm, Val)): (Tm, Val) =
    val (tm, ty) = inp
    tm match
      case Lam(_, Impl, _) => (tm, ty)
      case _               => insertPi(ctx, (tm, ty))

  private def insertUntilName(
      ctx: Ctx,
      name: Name,
      inp: (Tm, Val)
  ): (Tm, Val) =
    val (tm, ty) = inp
    force(ty) match
      case VPi(x, Impl, a, b) if x == name => (tm, ty)
      case VPi(x, Impl, a, b) =>
        val m = newMeta(ctx)
        val mv = ctx.eval(m)
        insertUntilName(ctx, name, (App(tm, m, Impl), vinst(b, mv)))
      case _ => throw NameNotInPiError(name)

  private def unifyCatch(ctx: Ctx, expected: Val, actual: Val): Unit =
    debug(s"unify: ${ctx.pretty(actual)} ~ ${ctx.pretty(expected)}")
    try unify(ctx.lvl, actual, expected)
    catch
      case e: UnifyError =>
        throw ElaborationUnifyError(
          s"${ctx.pretty(actual)} ~ ${ctx.pretty(expected)}: ${e.msg}\n${ctx.pos.longString}"
        )

  @tailrec
  def findNameInSigma(
      x: Name,
      tm: Val,
      ty: Val,
      i: Int = 0,
      xs: Set[Name] = Set.empty
  ): (Val, Int) = force(
    ty
  ) match
    case VSigma(y, ty, c) if x == y => (ty, i)
    case VSigma(y, ty, c) =>
      val name = if x == "_" || xs.contains(x) then None else Some(y)
      findNameInSigma(x, tm, vinst(c, vproj(tm, Named(name, i))), i + 1, xs + y)
    case _ => throw NameNotInSigmaError(x)

  private def inferImportLet(
      ctx: Ctx,
      stm: STm,
      ns: Option[List[Name]]
  ): (Ctx, Tm => Tm) =
    val (tm, ty) = infer(ctx, stm)
    val vtm = ctx.eval(tm)
    ns match
      case None =>
        def go(ctx: Ctx, tm: Tm, ty: Val, i: Int): (Ctx, Tm => Tm) =
          force(ty) match
            case VSigma(x, pty, b) if x != "_" =>
              val (nctx, builder) = go(
                ctx.define(x, pty, vproj(vtm, Named(Some(x), i))),
                tm.shift(1),
                vinst(b, vproj(vtm, Named(Some(x), i))),
                i + 1
              )
              (
                nctx,
                b =>
                  Let(
                    x,
                    ctx.quote(pty),
                    Proj(tm, Named(Some(x), i)),
                    builder(b)
                  )
              )
            case VSigma(x, ty, b) =>
              go(
                ctx.bind(x, Expl, ty),
                tm.shift(1),
                vinst(b, vproj(vtm, Named(None, i))),
                i + 1
              )
            case _ => (ctx, t => t)
        go(ctx, tm, ty, 0)
      case Some(ns) =>
        def go(ctx: Ctx, tm: Tm, ns: List[Name]): (Ctx, Tm => Tm) = ns match
          case Nil => (ctx, t => t)
          case x :: rest =>
            val (pty, i) = findNameInSigma(x, vtm, ty)
            val (nctx, builder) = go(
              ctx.define(x, pty, vproj(vtm, Named(Some(x), i))),
              tm.shift(1),
              rest
            )
            (
              nctx,
              b =>
                Let(x, ctx.quote(pty), Proj(tm, Named(Some(x), i)), builder(b))
            )
        go(ctx, tm, ns)

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
    debug(s"check: $tm : ${ctx.pretty(ty)}")
    (tm, force(ty)) match
      case (S.Hole(None), _) => newMeta(ctx)
      case (S.Hole(Some(name)), _) =>
        throw HoleError(s"_$name : ${ctx.pretty(ty)}\n${ctx.show}")
      case (S.Lam(x, i, tyopt, body), VPi(x2, i2, ty, b2))
          if i.fold(y => i2 == Impl && y == x2, _ == i2) =>
        tyopt match
          case None =>
          case Some(a) =>
            val ea = checkType(ctx, a)
            val va = ctx.eval(ea)
            unifyCatch(ctx, ty, va)
        Lam(x, i2, check(ctx.bind(x, i2, ty), body, ctx.inst(b2)))
      case (tm, VPi(x, Impl, a, b)) =>
        Lam(
          x,
          Impl,
          check(ctx.bind(x, Impl, a, true), tm, ctx.inst(b))
        )
      case (S.Let(x, oty, value, body), _) =>
        val (ety, vty, evalue) = checkOptionalTy(ctx, oty, value)
        val vvalue = ctx.eval(evalue)
        Let(x, ety, evalue, check(ctx.define(x, vty, vvalue), body, ty))
      case (S.ImportLet(tm, ns, body), _) =>
        val (nctx, etmbuilder) = inferImportLet(ctx, tm, ns)
        etmbuilder(check(nctx, body, ty))
      case (S.Pair(fst, snd), VSigma(x, a, b)) =>
        val efst = check(ctx, fst, a)
        val esnd = check(ctx, snd, vinst(b, ctx.eval(efst)))
        Pair(efst, esnd)
      case (tm, _) =>
        val (etm, tyAct) = insert(ctx, infer(ctx, tm))
        unifyCatch(ctx, ty, tyAct)
        etm

  private def checkType(ctx: Ctx, tm: STm): Tm = check(ctx, tm, VType)

  private def infer(ctx0: Ctx, tm: STm): (Tm, Val) =
    val ctx = ctx0.enter(tm.pos)
    debug(s"infer: $tm")
    tm match
      case S.Type => (Type, VType)
      case S.Var(name) =>
        getPrimitive(name) match
          case Some((_, ty)) => (Prim(name), ty)
          case None =>
            ctx.lookup(name) match
              case Some((ix, ty)) => (Var(ix), ty)
              case None =>
                getGlobal(name) match
                  case None => throw VarError(s"$name\n${ctx.pos.longString}")
                  case Some(ge) => (Global(name), ge.vty)
      case S.Let(x, oty, value, body) =>
        val (ety, vty, evalue) = checkOptionalTy(ctx, oty, value)
        val vvalue = ctx.eval(evalue)
        val (ebody, vbodyty) = infer(ctx.define(x, vty, vvalue), body)
        (Let(x, ety, evalue, ebody), vbodyty)
      case S.ImportLet(tm, ns, body) =>
        val (nctx, etmbuilder) = inferImportLet(ctx, tm, ns)
        val (ebody, vbodyty) = infer(nctx, body)
        (etmbuilder(ebody), vbodyty)
      case S.Pi(x, i, ty, body) =>
        val ety = checkType(ctx, ty)
        val ebody = checkType(ctx.bind(x, i, ctx.eval(ety)), body)
        (Pi(x, i, ety, ebody), VType)
      case S.Sigma(x, ty, body) =>
        val ety = checkType(ctx, ty)
        val ebody = checkType(ctx.bind(x, Expl, ctx.eval(ety)), body)
        (Sigma(x, ety, ebody), VType)
      case app @ S.App(fn, arg, j) =>
        val (i, efn, tty) = j match
          case Left(name) =>
            val (t, tty) = insertUntilName(ctx, name, infer(ctx, fn))
            (Impl, t, tty)
          case Right(Impl) =>
            val (t, tty) = infer(ctx, fn)
            (Impl, t, tty)
          case Right(Expl) =>
            val (t, tty) = insertPi(ctx, infer(ctx, fn))
            (Expl, t, tty)
        val (pt, rt) = force(tty) match
          case VPi(x, i2, a, b) =>
            if i != i2 then throw AppIcitMismatchError(app.toString)
            (a, b)
          case tty =>
            val a = ctx.eval(newMeta(ctx))
            val b = ClosEnv(ctx.env, newMeta(ctx.bind("x", i, a)))
            unifyCatch(ctx, VPi("x", i, a, b), tty)
            (a, b)
        val earg = check(ctx, arg, pt)
        (App(efn, earg, i), vinst(rt, ctx.eval(earg)))
      case proj @ S.Proj(t, p) =>
        val (tm, vt) = insertPi(ctx, infer(ctx, t))
        (force(vt), p) match
          case (VSigma(_, ty, _), SP.Fst) => (Proj(tm, Fst), ty)
          case (VSigma(_, _, c), SP.Snd) =>
            (Proj(tm, Snd), vinst(c, vfst(ctx.eval(tm))))
          case (tty, SP.Named(x)) =>
            val (a, i) = findNameInSigma(x, ctx.eval(tm), tty, 0, Set.empty)
            (Proj(tm, Named(Some(x), i)), a)
          case (tty, _) if p == SP.Fst || p == SP.Snd =>
            val a = ctx.eval(newMeta(ctx))
            val b = ctx.clos(newMeta(ctx.bind("x", Expl, a)))
            unifyCatch(ctx, VSigma("x", a, b), tty)
            p match
              case SP.Fst => (Proj(tm, Fst), a)
              case SP.Snd => (Proj(tm, Snd), vinst(b, vfst(ctx.eval(tm))))
              case _      => throw Impossible()
          case _ => throw NotSigmaError(proj.toString)
      case S.Lam(x, Right(i), tyopt, b) =>
        val va =
          ctx.eval(tyopt.map(ty => checkType(ctx, ty)).getOrElse(newMeta(ctx)))
        val (eb, vb) = insert(ctx, infer(ctx.bind(x, i, va), b))
        (Lam(x, i, eb), VPi(x, i, va, ctx.closeVal(vb)))
      case tm @ S.Lam(_, _, _, _) => throw NamedLambdaError(tm.toString)
      case S.Pair(fst, snd) =>
        val (efst, vtyfst) = infer(ctx, fst)
        val (esnd, vtysnd) = infer(ctx, snd)
        (Pair(efst, esnd), VSigma("_", vtyfst, ctx.closeVal(vtysnd)))
      case S.LabelLit(x) => (LabelLit(x), VPrimLabel)
      case S.Hole(None) =>
        val a = ctx.eval(newMeta(ctx))
        val t = newMeta(ctx)
        (t, a)
      case S.Hole(Some(name)) =>
        throw CannotInferError(s"named hole _${name}")

  def elaborate(tm: STm, pos: Position = NoPosition): (Tm, Tm) =
    resetMetas()
    val ctx = Ctx.empty(pos)
    val (etm, vty) = infer(ctx, tm)
    debug(s"elaboration done: $etm")
    val unsolved = unsolvedMetas()
    if unsolved.nonEmpty then
      throw UnsolvedMetasError(unsolved.map(id => s"?$id").mkString(", "))
    (ctx.zonk(etm), ctx.zonk(ctx.quote(vty)))

  def elaborateDecls(decls: Decls, pos: Position = NoPosition): Unit =
    decls.decls.foreach(elaborateDecl(_, pos))

  def elaborateDecl(decl: Decl, pos: Position = NoPosition): Unit = decl match
    case Import(_) =>
    case Def(x, v) =>
      if getGlobal(x).isDefined then throw GlobalError(x)
      val (etm, ety) = elaborate(v, pos)
      val vty = eval(Nil, ety)
      val vval = eval(Nil, etm)
      addGlobal(
        GlobalEntry(x, ety, vty, etm, vval, VGlobal(x, Nil, () => vval))
      )
