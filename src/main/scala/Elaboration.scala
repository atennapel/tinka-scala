import Common.*
import Presyntax.*
import Syntax.*
import Value.*
import Evaluation.*
import Unification.{unify as unify0}
import Globals.getGlobal
import Metas.*
import Errors.*
import scala.annotation.tailrec

object Elaboration:
  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    try unify0(a, b)(ctx.lvl)
    catch
      case e: UnifyError =>
        throw ElabUnifyError(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${e.msg}"
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

  @tailrec
  private def findNameInSigma(
      x: Name,
      tm: Val,
      ty: Val,
      map: Map[Name, Lvl],
      i: Int = 0,
      xs: Set[Name] = Set.empty
  )(implicit ctx: Ctx): (Val, Int) = force(
    ty
  ) match
    case VSigma(DoBind(y), ty, c) if x == y => (ty, i)
    case VSigma(y, ty, c) =>
      val name = y match
        case DoBind(y) if !xs.contains(y) => Some(y)
        case _                            => None
      findNameInSigma(
        x,
        tm,
        c.inst(vproj(tm, Named(name, i))),
        map,
        i + 1,
        name.map(xs + _).getOrElse(xs)
      )
    case _ => throw NameNotInSigmaError(x.toString)

  private def inferOpen(rtm: RTm, ns: Option[List[(Name, Option[Name])]])(
      implicit ctx: Ctx
  ): (Ctx, Tm => Tm) =
    val (tm, ty) = infer(rtm)
    val vtm = ctx.eval(tm)
    ns match
      case None =>
        def go(ctx: Ctx, tm: Tm, ty: Val, i: Int): (Ctx, Tm => Tm) =
          force(ty) match
            case VSigma(DoBind(x), pty, b) =>
              val (nctx, builder) = go(
                ctx.define(x, pty, vproj(vtm, Named(Some(x), i))),
                Wk(tm),
                b.inst(vproj(vtm, Named(Some(x), i))),
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
                ctx.bind(x, ty),
                Wk(tm),
                b.inst(vproj(vtm, Named(None, i))),
                i + 1
              )
            case _ => (ctx, t => t)
        go(ctx, tm, ty, 0)
      case Some(ns) =>
        def go(
            ctx: Ctx,
            tm: Tm,
            ns: List[(Name, Option[Name])],
            map: Map[Name, Lvl]
        ): (Ctx, Tm => Tm) = ns match
          case Nil => (ctx, t => t)
          case (x, oy) :: rest =>
            val y = oy.getOrElse(x)
            val (pty, i) = findNameInSigma(y, vtm, ty, map)
            val (nctx, builder) = go(
              ctx.define(x, pty, vproj(vtm, Named(Some(y), i))),
              Wk(tm),
              rest,
              map + (y -> ctx.lvl)
            )
            (
              nctx,
              b =>
                Let(
                  x,
                  ctx.quote(pty),
                  Proj(tm, Named(Some(y), i)),
                  builder(b)
                )
            )
        go(ctx, tm, ns, Map.empty)

  private def icitMatch(i1: RArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case RArgNamed(x) =>
      b match
        case DoBind(y) => x == y && i2 == Impl
        case DontBind  => false
    case RArgIcit(i) => i == i2

  private def check(tm: RTm, ty: VTy)(implicit ctx: Ctx): Tm =
    (tm, force(ty)) match
      case (RPos(pos, tm), _) => check(tm, ty)(ctx.enter(pos))
      case (RHole(ox), _) =>
        throw HoleError(
          s"hole ${ox.fold("_")(x => s"_$x")} : ${ctx.pretty(ty)}"
        )
      case (RLam(x, i, ot, b), VPi(y, i2, t, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => unify(ctx.eval(checkType(t0)), t))
        val eb = check(b, ctx.inst(rt))(ctx.bind(x, t))
        Lam(x, i2, eb)
      case (_, VPi(x, Impl, pty, rty)) =>
        val etm = check(tm, ctx.inst(rty))(ctx.bind(x, pty, true))
        Lam(x, Impl, etm)
      case (RPair(fst, snd), VSigma(_, fty, sty)) =>
        val efst = check(fst, fty)
        val esnd = check(snd, sty.inst(ctx.eval(efst)))
        Pair(efst, esnd)
      case (RLet(x, t, v, b), _) =>
        val (ev, et, vt) = checkValue(v, t)
        val eb = check(b, ty)(ctx.define(x, vt, ctx.eval(ev)))
        Let(x, et, ev, eb)
      case (ROpen(tm, ns, b), _) =>
        val (nctx, builder) = inferOpen(tm, ns)
        builder(check(b, ty)(nctx))
      case _ =>
        val (etm, vty) = infer(tm)
        unify(vty, ty)
        etm

  private def projIndex(tm: Val, x: Bind, ix: Int, clash: Boolean): Val =
    x match
      case DoBind(x) if !clash => vproj(tm, Named(Some(x), ix))
      case _ =>
        @tailrec
        def go(tm: Val, ix: Int): Val = ix match
          case 0 => vproj(tm, Fst)
          case n => go(vproj(tm, Snd), n - 1)
        go(tm, ix)
  private def projNamed(tm: Val, ty: VTy, x: Name)(implicit
      ctx: Ctx
  ): (ProjType, VTy) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy) =
      force(ty) match
        case VSigma(DoBind(y), fstty, _) if x == y =>
          (Named(Some(x), ix), fstty)
        case VSigma(y, _, sndty) =>
          val (clash, newns) = y match
            case DoBind(y) => (ns.contains(y), ns + y)
            case DontBind  => (false, ns)
          go(sndty.inst(projIndex(tm, y, ix, clash)), ix + 1, newns)
        case _ =>
          throw NotSigmaError(s"in named project $x, got ${ctx.pretty(ty)}")
    go(ty, 0, Set.empty)

  private def infer(tm: RTm)(implicit ctx: Ctx): (Tm, VTy) = tm match
    case RPos(pos, tm) => infer(tm)(ctx.enter(pos))
    case RType         => (Type, VType)
    case RUnitType     => (UnitType, VType)
    case RUnitValue    => (UnitValue, VUnitType)
    case RVar(x) =>
      ctx.lookup(x) match
        case Some((ix, ty)) => (Var(ix), ty)
        case None           => throw UndefVarError(x.toString)
    case RUri(uri) =>
      getGlobal(uri) match
        case Some(e) => (Uri(uri), e.vty)
        case None    => throw UndefUriError(uri.toString)
    case RLet(x, t, v, b) =>
      val (ev, et, vt) = checkValue(v, t)
      val (eb, rt) = infer(b)(ctx.define(x, vt, ctx.eval(ev)))
      (Let(x, et, ev, eb), rt)
    case ROpen(tm, ns, b) =>
      val (nctx, builder) = inferOpen(tm, ns)
      val (eb, rty) = infer(b)(nctx)
      (builder(eb), rty)
    case RPi(x, i, t, b) =>
      val et = checkType(t)
      val eb = checkType(b)(ctx.bind(x, ctx.eval(et)))
      (Pi(x, i, et, eb), VType)
    case RSigma(x, t, b) =>
      val et = checkType(t)
      val eb = checkType(b)(ctx.bind(x, ctx.eval(et)))
      (Sigma(x, et, eb), VType)
    case RApp(f, a, RArgIcit(i)) =>
      val (ef, ft) = infer(f)
      force(ft) match
        case VPi(_, i2, vt, b) if i == i2 =>
          val ea = check(a, vt)
          (App(ef, ea, i), b.inst(ctx.eval(ea)))
        case _ => throw NotPiError(s"$tm: ${ctx.pretty(ft)}")
    case RProj(tm, proj) =>
      val (etm, ty) = infer(tm)
      force(ty) match
        case VSigma(_, fty, sty) =>
          proj match
            case RFst => (Proj(etm, Fst), fty)
            case RSnd => (Proj(etm, Snd), sty.inst(vproj(ctx.eval(etm), Fst)))
            case RNamed(x) =>
              val (eproj, rty) = projNamed(ctx.eval(etm), ty, x)
              (Proj(etm, eproj), rty)
        case _ => throw NotSigmaError(s"$tm: ${ctx.pretty(ty)}")
    case RLam(x, RArgIcit(i), Some(t), b) =>
      val et = checkType(t)
      val vt = ctx.eval(et)
      val (eb, rt) = infer(b)(ctx.bind(x, vt))
      (Lam(x, i, eb), VPi(x, i, vt, ctx.close(rt)))
    case _ => throw CannotInferError(tm.toString)

  def elaborate(tm: RTm)(implicit ctx: Ctx = Ctx.empty()): (Tm, Ty) =
    resetMetas()
    val (etm, vty) = infer(tm)
    println(etm)
    println(vty)
    (etm, ctx.quote(vty))
