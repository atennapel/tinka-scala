import Common.*
import Core.*
import Surface as S
import Value.*
import Evaluation.*
import Unification.*
import Ctx.*
import Metas.*
import Errors.*
import Debug.*

import scala.annotation.tailrec

object Elaboration:
  private def newMeta(implicit ctx: Ctx): Tm =
    val m = freshMeta()
    InsertedMeta(m, ctx.bds)

  private def insertPi(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    @tailrec
    def go(tm: Tm, ty: VTy): (Tm, VTy) = ty.force match
      case VPi(x, Impl, a, b) =>
        val m = newMeta
        val mv = m.evalCtx
        go(App(tm, m, Impl), b(mv))
      case _ => (tm, ty)
    go(inp._1, inp._2)

  private def insert(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case _               => insertPi(inp)

  private def insertUntilName(x: Name, inp: (Tm, VTy))(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    def go(tm: Tm, ty: VTy): (Tm, VTy) = ty.force match
      case VPi(y, Impl, a, b) =>
        if x == y then (tm, ty)
        else
          val m = newMeta
          val mv = m.evalCtx
          go(App(tm, m, Impl), b(mv))
      case _ => throw NamedImplicitError(s"no implicit found with name $x")
    go(inp._1, inp._2)

  private def unify(a: Val, b: Val)(implicit ctx: Ctx): Unit =
    try unifyCtx(a, b)
    catch
      case err: UnifyError =>
        throw ElabUnifyError(s"${a.quoteCtx} ~ ${b.quoteCtx}: ${err.msg}")

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

  private def icitMatch(i1: S.ArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case S.ArgNamed(x) =>
      b match
        case DoBind(y) => x == y && i2 == Impl
        case DontBind  => false
    case S.ArgIcit(i) => i == i2

  private def check(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm =
    debug(s"check $tm : ${ty.quoteCtx}")
    (tm, ty.force) match
      case (S.Type, VType)     => Type
      case (S.UnitType, VType) => UnitType
      case (S.Unit, VUnitType) => Unit
      case (S.Hole, _)         => newMeta
      case (S.Lam(x, i, oty, b), VPi(y, i2, pty, rty)) if icitMatch(i, y, i2) =>
        oty.foreach(ty => unify(checkType(ty).evalCtx, pty))
        val eb = check(b, rty.underCtx)(ctx.bind(x, pty))
        Lam(x, i2, eb)
      case (tm, VPi(x, Impl, pty, rty)) =>
        val etm = check(tm, rty.underCtx)(ctx.bind(x, pty, true))
        Lam(x, Impl, etm)
      case (S.Pair(fst, snd), VSigma(_, fstty, sndty)) =>
        val efst = check(fst, fstty)
        val esnd = check(snd, sndty(efst.evalCtx))
        Pair(efst, esnd)
      case (S.Let(x, oty, v, b), _) =>
        val (ev, ety, vty) = checkOptionalType(v, oty)
        val eb = check(b, ty)(ctx.define(x, vty, ev.evalCtx))
        Let(x, ety, ev, eb)
      case _ =>
        val (etm, ty2) = insert(infer(tm))
        unify(ty2, ty)
        etm

  private def projIndex(tm: Val, x: Bind, ix: Int, clash: Boolean): Val =
    x match
      case DoBind(x) if !clash => tm.proj(Named(x, ix))
      case _ =>
        @tailrec
        def go(tm: Val, ix: Int): Val = ix match
          case 0 => tm.proj(Fst)
          case n => go(tm.proj(Snd), n - 1)
        go(tm, ix)
  private def projNamed(tm: Val, ty: VTy, x: Name)(implicit
      ctx: Ctx
  ): (ProjType, VTy) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy) = ty.force match
      case VSigma(DoBind(y), fstty, _) if x == y => (Named(x, ix), fstty)
      case VSigma(y, _, sndty) =>
        val (clash, newns) = y match
          case DoBind(y) => (ns.contains(y), ns + y)
          case DontBind  => (false, ns)
        go(sndty(projIndex(tm, y, ix, clash)), ix + 1, newns)
      case _ =>
        throw ExpectedSigmaError(s"in named project $x, got ${ty.quoteCtx}")
    go(ty, 0, Set.empty)

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
      case S.Pi(x, i, ty, b) =>
        val ety = checkType(ty)
        val eb = checkType(b)(ctx.bind(x, ety.evalCtx))
        (Pi(x, i, ety, eb), VType)
      case S.Sigma(x, ty, b) =>
        val ety = checkType(ty)
        val eb = checkType(b)(ctx.bind(x, ety.evalCtx))
        (Sigma(x, ety, eb), VType)
      case S.App(f, a, i) =>
        val (icit, ef, fty) = i match
          case S.ArgNamed(x) =>
            val (ef, fty) = insertUntilName(x, infer(f))
            (Impl, ef, fty)
          case S.ArgIcit(Impl) =>
            val (ef, fty) = infer(f)
            (Impl, ef, fty)
          case S.ArgIcit(Expl) =>
            val (ef, fty) = insertPi(infer(f))
            (Expl, ef, fty)
        val (pty, rty) = fty.force match
          case VPi(x, icit2, pty, rty) =>
            if icit != icit2 then throw IcitMismatchError(tm.toString)
            (pty, rty)
          case tty =>
            val pty = newMeta.evalCtx
            val rty = Clos(ctx.env, newMeta(ctx.bind(DoBind(Name("x")), pty)))
            unify(tty, VPi(DoBind(Name("x")), icit, pty, rty))
            (pty, rty)
        val ea = check(a, pty)
        (App(ef, ea, icit), rty(ea.evalCtx))
      case S.Proj(t, p) =>
        val (et, ty) = insertPi(infer(t))
        (ty.force, p) match
          case (_, S.Named(x)) =>
            val (p, pty) = projNamed(et.evalCtx, ty, x)
            (Proj(et, p), pty)
          case (VSigma(_, fstty, _), S.Fst) => (Proj(et, Fst), fstty)
          case (VSigma(_, _, sndty), S.Snd) =>
            (Proj(et, Snd), sndty(et.evalCtx.proj(Fst)))
          case (tty, S.Fst) =>
            val pty = newMeta.evalCtx
            val rty = Clos(ctx.env, newMeta(ctx.bind(DoBind(Name("x")), pty)))
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Fst), pty)
          case (tty, S.Snd) =>
            val pty = newMeta.evalCtx
            val rty = Clos(ctx.env, newMeta(ctx.bind(DoBind(Name("x")), pty)))
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Snd), rty(et.evalCtx.proj(Fst)))
      case S.Lam(x, S.ArgIcit(i), Some(ty), b) =>
        val vty = checkType(ty).evalCtx
        val (eb, rty) = insert(infer(b)(ctx.bind(x, vty)))
        (Lam(x, i, eb), VPi(x, i, vty, rty.closeCtx))
      case S.Lam(x, S.ArgIcit(i), None, b) =>
        val pty = newMeta.evalCtx
        val (eb, rty) = insert(infer(b)(ctx.bind(x, pty)))
        (Lam(x, i, eb), VPi(x, i, pty, rty.closeCtx))
      case S.Pair(fst, snd) =>
        val pty = newMeta.evalCtx
        val rty = Clos(ctx.env, newMeta(ctx.bind(DoBind(Name("x")), pty)))
        val ty = VSigma(DoBind(Name("x")), pty, rty)
        val ep = check(tm, ty)
        (ep, ty)
      case S.Hole =>
        val a = newMeta.evalCtx
        val t = newMeta
        (t, a)
      case S.Lam(_, _, _, _) => throw CannotInferError(tm.toString)

  def elaborate(tm: S.Tm): (Tm, Ty) =
    resetMetas()
    implicit val ctx = Ctx.empty
    val (etm, vty) = infer(tm)
    val ums = unsolvedMetas()
    if ums.nonEmpty then
      throw UnsolvedMetasError(ums.map(id => s"?$id").mkString(", "))
    (etm, vty.quoteCtx)
