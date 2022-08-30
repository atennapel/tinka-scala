import Common.*
import Core.*
import Surface as S
import Value.*
import Evaluation.*
import Ctx.*
import Metas.*
import Errors.*
import Debug.*
import Zonking.*
import Globals.*

import scala.annotation.tailrec

class Elaboration extends IElaboration:
  // unification
  private var unif: Option[IUnification] = None
  def setUnification(unif: IUnification): Unit = this.unif = Some(unif)

  private def unifyPlaceholder(tm: Tm, m: MetaId)(implicit ctx: Ctx): Unit =
    getMeta(m) match
      case Unsolved(bs, a) =>
        debug(s"solve unconstrained placeholder ?$m")
        val solution = tm.closeTmCtx
        debug(s"?$m := $solution")
        solveMeta(m, solution.eval(Nil), solution)
        bs.foreach(retryPostpone)
      case Solved(v, _, _) =>
        debug(s"unify solved placeholder ?$m")
        unif.get.unify(tm.evalCtx, vappPruning(v, ctx.pruning)(ctx.env))(
          ctx.lvl
        )

  override def retryPostpone(c: PostponeId): Unit = getPostpone(c) match
    case PostponeCheck(Unchecked(ctxU, t, a, lv, m)) =>
      implicit val ctx: Ctx = ctxU
      a.force match
        case VNe(HMeta(m2), _) => addBlocking(m2, c)
        case _ =>
          debug(s"retry check !$c with ?$m")
          val etm = check(t, a, lv)
          unifyPlaceholder(etm, m)
          solveCheck(c, etm)
    case PostponeUnify(UnifyPostpone(k, v1, v2)) =>
      debug(s"retry unify !$c: ${v1.quote(k)} ~ ${v2.quote(k)}")
      unif.get.unify(v1, v2)(k)
    case _ =>

  // TODO: do not postpone more at this stage
  private def checkEverything(): Unit =
    @tailrec
    def go(c: Int): Unit =
      val c2 = nextCheckId()
      if c < c2 then
        val id = postponeId(c)
        getPostpone(id) match
          case PostponeCheck(Unchecked(ctxU, t, a, lv, m)) =>
            implicit val ctx: Ctx = ctxU
            debug(s"check everything: !$c < !$c2")
            val (etm, ty, lv2) = insert(infer(t))
            solveCheck(id, etm)
            unify(lv2, lv, a, ty)
            unifyPlaceholder(etm, m)
          case PostponeUnify(UnifyPostpone(k, v1, v2)) =>
            debug(s"check everything: !$c < !$c2")
            unif.get.unify(v1, v2)(k)
          case _ =>
        go(c + 1)
    go(0)

  private def unify(u1: VLevel, u2: VLevel, a: Val, b: Val)(implicit
      ctx: Ctx
  ): Unit =
    try
      unif.get.unify(u1, u2)(ctx.lvl)
      unif.get.unify(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        throwCtx(
          ElabUnifyError(s"${a.prettyCtx} ~ ${b.quoteCtx}: ${err.msg}", _)
        )

  // elaboration
  private def newMeta(ty: VTy, lv: VLevel)(implicit ctx: Ctx): Tm = ty match
    case VUnitType => Unit
    case _ =>
      val closed = ty.quoteCtx.closeTyCtx(lv.quoteCtx).eval(Nil)
      val m = freshMeta(Set.empty, closed)
      debug(s"newMeta ?$m : ${ty.prettyCtx} : ${lv.prettyCtx} @ ${ctx.pruning}")
      AppPruning(Meta(m), ctx.pruning)

  private def newLMeta(implicit ctx: Ctx): FinLevel =
    val id = freshLMeta(ctx.lvl, ctx.levelVars)
    debug(s"newLMeta ?l$id ${ctx.levelVars.map(x => s"'$x").mkString(" ")}")
    LMeta(id)

  private enum InsertMode { case All; case LvlOnly; case NoLvl }
  import InsertMode.*
  private def insertPi(inp: (Tm, VTy, VLevel), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    @tailrec
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = ty.force match
      case VPi(x, Impl, a, u1, b, u2) if mode == All || mode == NoLvl =>
        val m = newMeta(a, u1)
        val mv = m.evalCtx
        go(App(tm, m, Impl), b(mv), u2)
      case VPiLvl(x, b, u) if mode == All || mode == LvlOnly =>
        val m = newLMeta
        val mv = m.evalCtx
        go(AppLvl(tm, m), b(mv), u(mv))
      case _ => (tm, ty, lv)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, VLevel))(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case LamLvl(_, _)    => inp
      case _               => insertPi(inp)

  private def insertUntilName(x: Name, inp: (Tm, VTy, VLevel))(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = ty.force match
      case VPi(y, Impl, a, u1, b, u2) =>
        if x == y then (tm, ty, lv)
        else
          val m = newMeta(a, u1)
          val mv = m.evalCtx
          go(App(tm, m, Impl), b(mv), u2)
      case VPiLvl(x, b, u) =>
        val m = newLMeta
        val mv = m.evalCtx
        go(AppLvl(tm, m), b(mv), u(mv))
      case _ =>
        throwCtx(NamedImplicitError(s"no implicit found with name $x", _))
    go(inp._1, inp._2, inp._3)

  private def insertUntilLevelName(x: Name, inp: (Tm, VTy, VLevel))(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = ty.force match
      case VPi(y, Impl, a, u1, b, u2) =>
        val m = newMeta(a, u1)
        val mv = m.evalCtx
        go(App(tm, m, Impl), b(mv), u2)
      case VPiLvl(y, b, u) =>
        if x == y then (tm, ty, lv)
        else
          val m = newLMeta
          val mv = m.evalCtx
          go(AppLvl(tm, m), b(mv), u(mv))
      case _ =>
        throwCtx(NamedImplicitError(s"no level implicit found with name $x", _))
    go(inp._1, inp._2, inp._3)

  private def inferType(ty: S.Ty)(implicit ctx: Ctx): (Ty, VLevel) =
    val (ety, u, lv) = infer(ty)
    u.force match
      case VType(l) => (ety, l)
      case _ =>
        val m = newLMeta.evalCtx
        val l = VFL(m)
        unify(lv, VFL(m + 1), u, VType(l))
        (ety, l)

  private def checkOptionalType(tm: S.Tm, ty: Option[S.Ty])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy, VLevel) =
    ty match
      case Some(ty) =>
        val (ety, lv) = inferType(ty)
        val vty = ety.evalCtx
        val etm = check(tm, vty, lv)
        (etm, ety, vty, lv)
      case None =>
        val (etm, vty, lv) = infer(tm)
        (etm, vty.quoteCtx, vty, lv)

  private def icitMatch(i1: S.ArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case S.ArgNamed(x) =>
      b match
        case DoBind(y) => x == y && i2 == Impl
        case DontBind  => false
    case S.ArgIcit(i) => i == i2
  private def lvlNameMatch(ox: Option[Name], b: Bind): Boolean = ox match
    case None => true
    case Some(x) =>
      b match
        case DoBind(y) => x == y
        case DontBind  => false

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    lookupCtx(x) match
      case Some((_, Some((vty, lv)))) =>
        vty.forceMetas match
          case VNe(HMeta(_), _) => true
          case _                => false
      case _ => throwCtx(UndefinedVarError(x.toString, _))

  private def shouldPostpone(t: S.Tm): Boolean = t match
    case S.Unit     => false
    case S.UnitType => false
    case _          => true

  private def check(tm: S.Tm, ty: VTy, lv: VLevel)(implicit ctx: Ctx): Tm =
    debug(s"check $tm : ${ty.quoteCtx}")
    (tm, ty.force) match
      case (S.SPos(pos, tm), _) => check(tm, ty, lv)(ctx.enter(pos))
      case (S.Hole, _)          => newMeta(ty, lv)
      case (S.Lam(x, i, oty, b), VPi(y, i2, pty, u1, rty, u2))
          if icitMatch(i, y, i2) =>
        oty.foreach(ty =>
          val (ety, lvty) = inferType(ty)
          unify(lvty, u1, ety.evalCtx, pty)
        )
        val eb = check(b, rty.underCtx, u2)(ctx.bind(x, pty, u1))
        Lam(x, i2, eb)
      case (S.LamLvl(x, i, b), VPiLvl(y, rty, u)) if lvlNameMatch(i, y) =>
        val v = VFinLevel.vr(ctx.lvl)
        val eb = check(b, rty(v), u(v))(ctx.bindLevel(x))
        LamLvl(x, eb)
      case (S.Var(x), VPi(_, Impl, _, _, _, _)) if hasMetaType(x) =>
        val Some((ix, Some((varty, lv1)))) = lookupCtx(x)
        unify(lv1, lv, varty, ty)
        Var(ix)
      case (S.Var(x), VPiLvl(_, _, _)) if hasMetaType(x) =>
        val Some((ix, Some((varty, lv1)))) = lookupCtx(x)
        unify(lv1, lv, varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl, pty, u1, rty, u2)) =>
        val etm = check(tm, rty.underCtx, u2)(ctx.bind(x, pty, u1, true))
        Lam(x, Impl, etm)
      case (tm, VPiLvl(x, rty, u)) =>
        val v = VFinLevel.vr(ctx.lvl)
        val etm = check(tm, rty(v), u(v))(ctx.bindLevel(x, true))
        LamLvl(x, etm)
      case (tm, VNe(HMeta(m), _)) if shouldPostpone(tm) =>
        val placeholder = freshMeta(Set.empty, ty.closeVTyCtx(lv.quoteCtx))
        val c = freshCheck(tm, ty, lv, placeholder)
        addBlocking(m, c)
        debug(s"postpone $tm : ${ty.quoteCtx} as ?$placeholder")
        PostponedCheck(c)
      case (S.Pair(fst, snd), VSigma(_, fstty, u1, sndty, u2)) =>
        val efst = check(fst, fstty, u1)
        val esnd = check(snd, sndty(efst.evalCtx), u2)
        Pair(efst, esnd)
      case (S.Let(x, oty, v, b), _) =>
        val (ev, ety, vty, lv1) = checkOptionalType(v, oty)
        val eb = check(b, ty, lv)(ctx.define(x, vty, ety, lv1, ev.evalCtx, ev))
        Let(x, ety, ev, eb)
      case _ =>
        val (etm, ty2, lv2) = insert(infer(tm))
        unify(lv2, lv, ty2, ty)
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
  ): (ProjType, VTy, VLevel) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy, VLevel) =
      ty.force match
        case VSigma(DoBind(y), fstty, u1, _, _) if x == y =>
          (Named(x, ix), fstty, u1)
        case VSigma(y, _, _, sndty, _) =>
          val (clash, newns) = y match
            case DoBind(y) => (ns.contains(y), ns + y)
            case DontBind  => (false, ns)
          go(sndty(projIndex(tm, y, ix, clash)), ix + 1, newns)
        case _ =>
          throwCtx(
            ExpectedSigmaError(s"in named project $x, got ${ty.quoteCtx}", _)
          )
    go(ty, 0, Set.empty)

  private def inferFinLevel(l: S.Level)(implicit ctx: Ctx): FinLevel = l match
    case S.LSPos(pos, l) => inferFinLevel(l)(ctx.enter(pos))
    case S.LVar(x) =>
      lookupCtx(x) match
        case Some((ix, None)) => LVar(ix)
        case _                => throwCtx(UndefinedVarError(x.toString, _))
    case S.LZ         => LZ
    case S.LS(a)      => LS(inferFinLevel(a))
    case S.LMax(a, b) => inferFinLevel(a) max inferFinLevel(b)
    case S.LHole      => newLMeta

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, VLevel) =
    debug(s"infer $tm")
    tm match
      case S.SPos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.Type(l) =>
        val el = inferFinLevel(l)
        val vl = el.evalCtx
        (Type(LFinLevel(el)), VType(VFL(vl + 1)), VFL(vl + 2))
      case S.UnitType => (UnitType, VType(VLevel.unit), VFL(VFinLevel.unit + 1))
      case S.Unit     => (Unit, VUnitType, VLevel.unit)
      case S.Var(x) =>
        lookupCtx(x) match
          case Some((ix, Some((vty, lv)))) => (Var(ix), vty, lv)
          case _ =>
            getGlobal(x) match
              case Some((GlobalEntry(_, vty, lv, value), lvl)) =>
                (Global(x, lvl), vty, lv)
              case _ => throwCtx(UndefinedVarError(x.toString, _))
      case S.Let(x, oty, v, b) =>
        val (ev, ety, vty, vl) = checkOptionalType(v, oty)
        val (eb, rty, vl1) =
          infer(b)(ctx.define(x, vty, ety, vl, ev.evalCtx, ev))
        (Let(x, ety, ev, eb), rty, vl1)
      case S.Pi(x, i, ty, b) =>
        val (ety, l1) = inferType(ty)
        val (eb, l2) = inferType(b)(ctx.bind(x, ety.evalCtx, l1))
        val u = l1 max l2
        (Pi(x, i, ety, l1.quoteCtx, eb, l2.quoteCtx), VType(u), u.inc)
      case S.Sigma(x, ty, b) =>
        val (ety, l1) = inferType(ty)
        val (eb, l2) = inferType(b)(ctx.bind(x, ety.evalCtx, l1))
        val u = l1 max l2
        (Sigma(x, ety, l1.quoteCtx, eb, l2.quoteCtx), VType(u), u.inc)
      case S.PiLvl(x, b) =>
        val (eb, l) = inferType(b)(ctx.bindLevel(x))
        (PiLvl(x, eb, l.quote(ctx.lvl + 1)), VType(VOmega), VOmega1)
      case S.App(f, a, i) =>
        val (icit, ef, fty, flv) = i match
          case S.ArgNamed(x) =>
            val (ef, fty, flv) = insertUntilName(x, infer(f))
            (Impl, ef, fty, flv)
          case S.ArgIcit(Impl) =>
            val (ef, fty, lv) = insertPi(infer(f), LvlOnly)
            (Impl, ef, fty, lv)
          case S.ArgIcit(Expl) =>
            val (ef, fty, lv) = insertPi(infer(f))
            (Expl, ef, fty, lv)
        val (pty, u1, rty, u2) = fty.force match
          case VPi(x, icit2, pty, u1, rty, u2) =>
            if icit != icit2 then throwCtx(IcitMismatchError(tm.toString, _))
            (pty, u1, rty, u2)
          case tty =>
            val l1 = newLMeta
            val u1 = VFL(l1.evalCtx)
            val l2 = newLMeta
            val u2 = VFL(l1.evalCtx)
            val pty = newMeta(VType(u1), u1.inc).evalCtx
            val x = DoBind(Name("x"))
            val rty =
              CClos[Val](
                ctx.env,
                newMeta(VType(u2), u2.inc)(ctx.bind(x, pty, u1))
              )
            unify(flv, u1 max u2, tty, VPi(x, icit, pty, u1, rty, u2))
            (pty, rty)
        val ea = check(a, pty, u1)
        (App(ef, ea, icit), rty(ea.evalCtx), u2)
      case S.AppLvl(f, a, i) =>
        val (ef, fty, flv) = i match
          case None       => insertPi(infer(f), NoLvl)
          case Some(name) => insertUntilLevelName(name, infer(f))
        val (rty, clvl) = fty.force match
          case VPiLvl(x, rty, u) => (rty, u)
          case tty =>
            val x = DoBind(Name("l"))
            val l1 = newLMeta
            val vl1 = l1.evalCtx
            val u = VFL(vl1)
            val clvl = ClosLvl(ctx.env, LFinLevel(l1))
            val rty = CClos[VFinLevel](
              ctx.env,
              newMeta(VType(u), u.inc)(ctx.bindLevel(x))
            )
            unify(flv, VOmega, tty, VPiLvl(x, rty, clvl))
            (rty, clvl)
        val ea = inferFinLevel(a)
        val vea = ea.evalCtx
        (AppLvl(ef, ea), rty(vea), clvl(vea))
      case S.Proj(t, p) =>
        val (et, ty, l1) = insertPi(infer(t))
        (ty.force, p) match
          case (_, S.Named(x)) =>
            val (p, pty, lv) = projNamed(et.evalCtx, ty, x)
            (Proj(et, p), pty, lv)
          case (VSigma(_, fstty, u1, _, _), S.Fst) => (Proj(et, Fst), fstty, u1)
          case (VSigma(_, _, _, sndty, u2), S.Snd) =>
            (Proj(et, Snd), sndty(et.evalCtx.proj(Fst)), u2)
          case (tty, S.Fst) =>
            val u1 = VFL(newLMeta.evalCtx)
            val u2 = VFL(newLMeta.evalCtx)
            val pty = newMeta(VType(u1), u1.inc).evalCtx
            val rty =
              CClos[Val](
                ctx.env,
                newMeta(VType(u2), u2.inc)(ctx.bind(DoBind(Name("x")), pty, u1))
              )
            unify(
              l1,
              u1 max u2,
              tty,
              VSigma(DoBind(Name("x")), pty, u1, rty, u2)
            )
            (Proj(et, Fst), pty, u1)
          case (tty, S.Snd) =>
            val u1 = VFL(newLMeta.evalCtx)
            val u2 = VFL(newLMeta.evalCtx)
            val pty = newMeta(VType(u1), u1.inc).evalCtx
            val rty =
              CClos[Val](
                ctx.env,
                newMeta(VType(u2), u2.inc)(ctx.bind(DoBind(Name("x")), pty, u1))
              )
            unify(
              l1,
              u1 max u2,
              tty,
              VSigma(DoBind(Name("x")), pty, u1, rty, u2)
            )
            (Proj(et, Snd), rty(et.evalCtx.proj(Fst)), u2)
      case S.Lam(x, S.ArgIcit(i), mty, b) =>
        val (pty, lv1) = (mty match
          case Some(ty) =>
            val (ety, lv) = inferType(ty)
            (ety.evalCtx, lv)
          case None =>
            val u = VFL(newLMeta.evalCtx)
            val m = newMeta(VType(u), u.inc)
            (m.evalCtx, u)
        )
        val ctx2 = ctx.bind(x, pty, lv1)
        val (eb, rty, lv2) = insert(infer(b)(ctx2))(ctx2)
        (Lam(x, i, eb), VPi(x, i, pty, lv1, rty.closeCtx, lv2), lv1 max lv2)
      case S.LamLvl(x, None, b) =>
        val ctx2 = ctx.bindLevel(x)
        val (eb, rty, u) = insert(infer(b)(ctx2))(ctx2)
        (
          LamLvl(x, eb),
          VPiLvl(x, rty.closeCtx, ClosLvl(ctx.env, u.quote(ctx.lvl + 1))),
          VOmega
        )
      case S.Pair(fst, snd) =>
        val (efst, fstty, u1) = infer(fst)
        val (esnd, sndty, u2) = infer(snd)
        (
          Pair(efst, esnd),
          VSigma(DontBind, fstty, u1, CFun(_ => sndty), u2),
          u1 max u2
        )
      case S.Hole =>
        val l = newLMeta
        val u = VFL(l.evalCtx)
        val a = newMeta(VType(u), u.inc).evalCtx
        val t = newMeta(a, u)
        (t, a, u)
      case S.Lam(_, _, _, _) =>
        throwCtx(CannotInferError("lambda with named parameter", _))
      case S.LamLvl(_, _, _) =>
        throwCtx(CannotInferError("level lambda with named parameter", _))

  def elaborate(tm: S.Tm, ctx0: Ctx = Ctx.empty): (Tm, Ty, Level) =
    reset()
    implicit val ctx = ctx0
    val (etm, vty, lv) = infer(tm)
    checkEverything()
    val ztm = etm.zonkCtx
    val zty = vty.quoteCtx.zonkCtx
    val zlv = lv.quoteCtx.zonkCtx
    val ums = unsolvedMetas()
    val ulms = unsolvedLMetas()
    if ums.nonEmpty || ulms.nonEmpty then
      throwCtx(
        UnsolvedMetasError(
          s"\n${ztm.prettyCtx} : ${zty.prettyCtx} : ${zlv.prettyCtx}\n${ums
              .map((id, ty) => s"?$id : ${ty.prettyCtx}")
              .mkString("\n")}\nunsolved universe level metas: ${ulms
              .map(id => s"?l$id")
              .mkString(", ")}",
          _
        )
      )
    (ztm, zty, zlv)

  def elaborateTop(tm: S.Tm, ctx0: Ctx = Ctx.empty): (Tm, Ty, Level) =
    implicit val ctx: Ctx = ctx0
    tm match
      case S.SPos(pos, tm) => elaborateTop(tm, ctx.enter(pos))
      case S.Let(x, oty, v, b) =>
        val (etm, ety, elv) = elaborate(S.Let(x, oty, v, S.Var(x)), ctx)
        addGlobal(GlobalEntry(x, ety.eval(Nil), elv.eval(Nil), etm.eval(Nil)))
        elaborateTop(b, ctx)
      case _ => elaborate(tm, ctx)
