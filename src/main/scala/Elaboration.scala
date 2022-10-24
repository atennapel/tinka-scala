import Common.*
import Presyntax.*
import Syntax.*
import Value.*
import Evaluation.*
import Globals.getGlobal
import Metas.*
import Errors.*
import Prims.*
import Debug.debug

import scala.annotation.tailrec
import java.io.Closeable
import scala.collection.mutable

class Elaboration extends IElaboration:
  // unification
  private var unif: Option[IUnification] = None
  def setUnification(unif: IUnification): Unit = this.unif = Some(unif)

  override def retryCheck(c: CheckId): Unit = getCheck(c) match
    case Unchecked(ctxU, t, a, m) =>
      implicit val ctx: Ctx = ctxU
      force(a) match
        case VFlex(m2, _) => addBlocking(m2, c)
        case _ =>
          debug(s"retry check !$c with ?$m")
          val etm = check(t, a)
          unifyPlaceholder(etm, m)
          solveCheck(c, etm)
    case _ =>

  private def unifyPlaceholder(tm: Tm, m: MetaId)(implicit ctx: Ctx): Unit =
    getMeta(m) match
      case Unsolved(bs, a) =>
        debug(s"solve unconstrained placeholder ?$m")
        val solution = ctx.closeTm(tm)
        debug(s"?$m := $solution")
        solveMeta(m, eval(solution)(Nil), solution)
        bs.foreach(retryCheck)
      case Solved(v, _, _) =>
        debug(s"unify solved placeholder ?$m")
        unif.get.unify(ctx.eval(tm), vappPruning(v, ctx.pruning)(ctx.env))(
          ctx.lvl
        )

  private def checkEverything(): Unit =
    @tailrec
    def go(c: Int): Unit =
      val c2 = nextCheckId()
      if c < c2 then
        val id = checkId(c)
        getCheck(id) match
          case Unchecked(ctxU, t, a, m) =>
            implicit val ctx: Ctx = ctxU
            debug(s"check everything: !$c < !$c2")
            val (etm, ty) = insert(infer(t))
            solveCheck(id, etm)
            unify(a, ty)
            unifyPlaceholder(etm, m)
          case _ =>
        go(c + 1)
    go(0)

  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try unif.get.unify(a, b)(ctx.lvl)
    catch
      case e: UnifyError =>
        throw ElabUnifyError(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${e.msg}"
        )

  // holes
  private val holes: mutable.Map[Name, HoleEntry] = mutable.Map.empty

  private case class HoleEntry(ctx: Ctx, tm: Tm, ty: VTy)

  // insertion
  private def newMeta(ty: VTy)(implicit ctx: Ctx): Tm = ty match
    case VUnitType() => UnitValue
    case _ =>
      val closed = ctx.closeVTy(ty)
      val m = freshMeta(Set.empty, closed)
      debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
      AppPruning(Meta(m), ctx.pruning)

  private def insertPi(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    @tailrec
    def go(tm: Tm, ty: VTy): (Tm, VTy) = force(ty) match
      case VPi(x, Impl, a, b) =>
        val m = newMeta(a)
        val mv = ctx.eval(m)
        go(App(tm, m, Impl), b.inst(mv))
      case _ => (tm, ty)
    go(inp._1, inp._2)

  private def insert(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case _               => insertPi(inp)

  private def insertUntilName(x: Name, inp: (Tm, VTy))(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    def go(tm: Tm, ty: VTy): (Tm, VTy) = force(ty) match
      case VPi(y, Impl, a, b) =>
        y match
          case DoBind(yy) if x == yy => (tm, ty)
          case _ =>
            val m = newMeta(a)
            val mv = ctx.eval(m)
            go(App(tm, m, Impl), b.inst(mv))
      case _ => throw NamedImplicitError(x.toString)
    go(inp._1, inp._2)

  // elaboration
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

  private def namesFromSigma(ty: Val)(implicit ctx: Ctx): List[Name] =
    force(ty) match
      case VSigma(bd @ DoBind(x), ty, b) =>
        x :: namesFromSigma(b.inst(VVar(ctx.lvl)))(ctx.bind(bd, ty))
      case VSigma(bd, ty, b) =>
        namesFromSigma(b.inst(VVar(ctx.lvl)))(ctx.bind(bd, ty))
      case _ => Nil

  @tailrec
  private def findNameInSigma(
      x: Name,
      tm: Val,
      ty: Val,
      map: Map[Name, Lvl],
      i: Int = 0,
      xs: Set[Name] = Set.empty
  )(implicit ctx: Ctx): (Val, Int) =
    force(ty) match
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

  private def inferOpen(
      rtm: RTm,
      ns: Option[List[(Name, Option[Name])]],
      hiding: Set[Name]
  )(implicit ctx: Ctx): (Ctx, Tm => Tm) =
    val (tm, ty) = infer(rtm)
    val vtm = ctx.eval(tm)
    def go(
        ctx: Ctx,
        tm: Tm,
        ns: List[(Name, Option[Name])],
        map: Map[Name, Lvl]
    ): (Ctx, Tm => Tm) = ns match
      case Nil => (ctx, t => t)
      case (x, oy) :: rest =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then go(ctx, tm, rest, map)
        else
          val (pty, i) = findNameInSigma(y, vtm, ty, map)
          val value = vproj(vtm, Named(Some(y), i))
          val (nctx, builder) = go(
            ctx.define(
              x,
              pty,
              ctx.quote(pty),
              value,
              ctx.quote(value)
            ), // TODO: local gluing
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
    go(ctx, tm, ns.getOrElse(namesFromSigma(ty).map(x => (x, None))), Map.empty)

  private def inferExport(
      ns: Option[List[(Name, Option[Name])]],
      hiding: Set[Name]
  )(implicit ctx: Ctx): (Tm, VTy) =
    def go(ctx: Ctx, ns: List[(Name, Option[Name])]): Tm = ns match
      case Nil => UnitValue
      case (x, oy) :: ns =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then go(ctx, ns)
        else
          val (ix, _) = ctx.lookup(y).get
          Pair(Var(ix), go(ctx, ns))
    def goTy(ctx: Ctx, ns: List[(Name, Option[Name])]): Tm = ns match
      case Nil => UnitType
      case (x, oy) :: ns =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then
          val (_, ty) = ctx.lookup(y).get
          goTy(ctx.bind(DoBind(y), ty), ns)
        else
          val (ix, ty) = ctx.lookup(y).get
          Sigma(DoBind(x), ctx.quote(ty), goTy(ctx.bind(DoBind(y), ty), ns))
    val xs = ns.getOrElse(ctx.names.reverse.map(x => (x, None)))
    val tm = go(ctx, xs)
    val ty = ctx.eval(goTy(ctx, xs))
    (tm, ty)

  private def icitMatch(i1: RArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case RArgNamed(x) =>
      b match
        case DoBind(y) => x == y && i2 == Impl
        case DontBind  => false
    case RArgIcit(i) => i == i2

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some((_, vty)) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def shouldPostpone(t: RTm): Boolean = t match
    case RVar(Name("()")) => false
    case RVar(Name("[]")) => false
    case RVar(_)          => false
    case RApp(_, _, _)    => false
    case _                => true

  private def check(tm: RTm, ty: VTy)(implicit ctx: Ctx): Tm =
    debug(s"check $tm : ${ctx.pretty(ty)}")
    (tm, force(ty)) match
      case (RPos(pos, tm), _) => check(tm, ty)(ctx.enter(pos))
      case (RHole(None), _)   => newMeta(ty)
      case (RHole(Some(x)), _) =>
        val t = newMeta(ty)
        holes += x -> HoleEntry(ctx, t, ty)
        t
      case (RLam(x, i, ot, b), VPi(y, i2, t, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => unify(ctx.eval(checkType(t0)), t))
        val eb = check(b, ctx.inst(rt))(ctx.bind(x, t))
        Lam(x, i2, eb)
      case (RVar(x), VPi(_, Impl, _, _)) if hasMetaType(x) =>
        val Some((ix, varty)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        Var(ix)
      case (_, VPi(x, Impl, pty, rty)) =>
        val etm = check(tm, ctx.inst(rty))(ctx.bind(x, pty, true))
        Lam(x, Impl, etm)
      case (tm, VFlex(m, _)) if shouldPostpone(tm) =>
        val placeholder = freshMeta(Set.empty, ctx.closeVTy(ty))
        val c = freshCheck(ctx, tm, ty, placeholder)
        addBlocking(m, c)
        debug(s"postpone $tm : ${ctx.pretty(ty)} as ?$placeholder")
        PostponedCheck(c)
      case (RPair(fst, snd), VSigma(_, fty, sty)) =>
        val efst = check(fst, fty)
        val esnd = check(snd, sty.inst(ctx.eval(efst)))
        Pair(efst, esnd)
      case (RLet(x, t, v, b), _) =>
        val (ev, et, vt) = checkValue(v, t)
        val eb = check(b, ty)(ctx.define(x, vt, et, ctx.eval(ev), ev))
        Let(x, et, ev, eb)
      case (ROpen(tm, ns, hiding, b), _) =>
        val (nctx, builder) = inferOpen(tm, ns, hiding.toSet)
        builder(check(b, ty)(nctx))
      // sugar
      case (RVar(Name("[]")), VId(_, _, _, _)) => check(RVar(Name("Refl")), ty)
      case (RVar(Name("[]")), VFix(_, _, _)) =>
        check(RApp(RVar(Name("Roll")), tm, RArgIcit(Expl)), ty)
      case (RPair(_, _), VFix(_, _, _)) =>
        check(RApp(RVar(Name("Roll")), tm, RArgIcit(Expl)), ty)
      // switch to infer
      case _ =>
        val (etm, vty) = insert(infer(tm))
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

  private def infer(tm: RTm)(implicit ctx: Ctx): (Tm, VTy) =
    debug(s"infer $tm")
    tm match
      case RPos(pos, tm) => infer(tm)(ctx.enter(pos))
      case RType         => (Type, VType)
      case RVar(x) =>
        ctx.lookup(x) match
          case Some((ix, ty)) => (Var(ix), ty)
          case None =>
            PrimName(x) match
              case Some(p) => (Prim(p), primType(p.fold(x => x, x => x)))
              case None    => throw UndefVarError(x.toString)
      case RUri(uri) =>
        getGlobal(uri) match
          case Some(e) => (Uri(uri), e.vty)
          case None    => throw UndefUriError(uri.toString)
      case RLet(x, t, v, b) =>
        val (ev, et, vt) = checkValue(v, t)
        val (eb, rt) = infer(b)(ctx.define(x, vt, et, ctx.eval(ev), ev))
        (Let(x, et, ev, eb), rt)
      case ROpen(tm, ns, hiding, b) =>
        val (nctx, builder) = inferOpen(tm, ns, hiding.toSet)
        val (eb, rty) = infer(b)(nctx)
        (builder(eb), rty)
      case RExport(ns, hiding) => inferExport(ns, hiding.toSet)
      case RPi(x, i, t, b) =>
        val et = checkType(t)
        val eb = checkType(b)(ctx.bind(x, ctx.eval(et)))
        (Pi(x, i, et, eb), VType)
      case RSigma(x, t, b) =>
        val et = checkType(t)
        val eb = checkType(b)(ctx.bind(x, ctx.eval(et)))
        (Sigma(x, et, eb), VType)
      case RApp(f, a, i) =>
        val (icit, ef, fty) = i match
          case RArgNamed(x) =>
            val (ef, fty) = insertUntilName(x, infer(f))
            (Impl, ef, fty)
          case RArgIcit(Impl) =>
            val (ef, fty) = infer(f)
            (Impl, ef, fty)
          case RArgIcit(Expl) =>
            val (ef, fty) = insertPi(infer(f))
            (Expl, ef, fty)
        val (pty, rty) = force(fty) match
          case VPi(x, icit2, pty, rty) =>
            if icit != icit2 then throw IcitMismatchError(tm.toString)
            (pty, rty)
          case tty =>
            val pty = ctx.eval(newMeta(VType))
            val x = DoBind(Name("x"))
            val rty = Clos(newMeta(VType)(ctx.bind(x, pty)))(ctx.env)
            unify(tty, VPi(x, icit, pty, rty))
            (pty, rty)
        val ea = check(a, pty)
        (App(ef, ea, icit), rty.inst(ctx.eval(ea)))
      case RProj(t, p) =>
        val (et, ty) = insertPi(infer(t))
        (force(ty), p) match
          case (_, RNamed(x)) =>
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p), pty)
          case (VSigma(_, fstty, _), RFst) => (Proj(et, Fst), fstty)
          case (VSigma(_, _, sndty), RSnd) =>
            (Proj(et, Snd), sndty.inst(vproj(ctx.eval(et), Fst)))
          case (tty, RFst) =>
            val pty = ctx.eval(newMeta(VType))
            val rty =
              Clos(
                newMeta(VType)(ctx.bind(DoBind(Name("x")), pty))
              )(ctx.env)
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Fst), pty)
          case (tty, RSnd) =>
            val pty = ctx.eval(newMeta(VType))
            val rty =
              Clos(newMeta(VType)(ctx.bind(DoBind(Name("x")), pty)))(ctx.env)
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Snd), rty.inst(vproj(ctx.eval(et), Fst)))
      case RLam(x, RArgIcit(i), mty, b) =>
        val pty = mty match
          case Some(ty) => ctx.eval(checkType(ty))
          case None     => ctx.eval(newMeta(VType))
        val ctx2 = ctx.bind(x, pty)
        val (eb, rty) = insert(infer(b)(ctx2))(ctx2)
        (Lam(x, i, eb), VPi(x, i, pty, ctx.close(rty)))
      case RPair(fst, snd) =>
        val (efst, fstty) = infer(fst)
        val (esnd, sndty) = infer(snd)
        (
          Pair(efst, esnd),
          VSigma(DontBind, fstty, Clos(ctx.quote(sndty))(ctx.env))
        )
      case RHole(None) =>
        val a = ctx.eval(newMeta(VType))
        val t = newMeta(a)
        (t, a)
      case RHole(Some(x)) =>
        val a = ctx.eval(newMeta(VType))
        val t = newMeta(a)
        holes += x -> HoleEntry(ctx, t, a)
        (t, a)
      case _ => throw CannotInferError(tm.toString)

  private def prettyHoles(implicit ctx0: Ctx): String =
    holes
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty) =>
            s"_$x : ${ctx.pretty(vty)} = ${ctx.pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  def elaborate(tm: RTm)(implicit ctx: Ctx): (Tm, Ty) =
    // resetMetas() TODO: zonking
    holes.clear()
    val (etm, vty) = infer(tm)
    checkEverything()
    val ety = ctx.quote(vty)
    if holes.nonEmpty then
      throw HoleError(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)}\n\n${prettyHoles}"
      )
    (etm, ety)
