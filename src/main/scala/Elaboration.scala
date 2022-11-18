import Common.*
import Presyntax.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*
import Errors.*
import Unification.{unify as unify0}
import Prims.getPrimType
import Globals.getGlobal
import Debug.debug

import scala.annotation.tailrec
import java.io.Closeable
import scala.collection.mutable

object Elaboration:
  // unification
  private def unify(u1: VLevel, u2: VLevel, a: Val, b: Val)(implicit
      ctx: Ctx
  ): Unit =
    try
      debug(s"unify ${ctx.pretty(u1)} ~ ${ctx.pretty(u2)}")
      unify0(u1, u2)(ctx.lvl)
      debug(s"${ctx.quote(a)} ~ ${ctx.quote(b)}")
      debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
      unify0(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        try
          debug(s"unifying levels failed try types first")
          debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          unify0(a, b)(ctx.lvl)
          debug(s"unify ${ctx.pretty(u1)} ~ ${ctx.pretty(u2)}")
          unify0(u1, u2)(ctx.lvl)
        catch
          case err: UnifyError =>
            throw ElabUnifyError(
              s"${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
            )

  private def unify(a: Val, b: Val)(implicit ctx: Ctx): Unit =
    try
      debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
      unify0(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        throw ElabUnifyError(
          s"${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  private def unify(a: VLevel, b: VLevel)(implicit ctx: Ctx): Unit =
    try
      debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
      unify0(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        throw ElabUnifyError(
          s"${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  // holes
  private val holes: mutable.Map[Name, HoleEntry] = mutable.Map.empty

  private case class HoleEntry(ctx: Ctx, tm: Tm, ty: VTy, lv: VLevel)

  // elaboration
  private def newMeta(ty: VTy, lv: VLevel)(implicit ctx: Ctx): Tm = ty match
    case VUnitType() => Prim(PUnit)
    case _ =>
      val closed = eval(ctx.closeTy(ctx.quote(ty), ctx.quote(lv)))(EEmpty)
      val m = freshMeta(closed)
      debug(s"newMeta ?$m : ${ctx.pretty(ty)} : ${ctx.pretty(lv)}")
      AppPruning(Meta(m), ctx.pruning)

  private def newLMeta(implicit ctx: Ctx): FinLevel =
    val id = freshLMeta()
    debug(s"newLMeta ?l$id")
    LInsertedMeta(id, ctx.levelPruning)

  private enum InsertMode:
    case All
    case Until(i: ImplMode)
    case NoLvl
    def isUntil: Boolean = this match
      case Until(_) => true
      case _        => false
    def isUntil(i: ImplMode): Boolean = this match
      case Until(j) => i == j
      case _        => false
  import InsertMode.*
  private def insertPi(inp: (Tm, VTy, VLevel), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    @tailrec
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = force(ty) match
      case VPi(x, Impl(i), a, u1, b, u2)
          if mode == All || mode == NoLvl || !mode.isUntil(i) =>
        val m = newMeta(a, u1)
        val mv = ctx.eval(m)
        go(App(tm, m, Impl(i)), b.inst(mv), u2)
      case VPiLvl(x, b, u) if mode == All || mode.isUntil =>
        val m = newLMeta
        val mv = ctx.eval(m)
        go(AppLvl(tm, m), b.inst(mv), u.inst(mv))
      case _ => (tm, ty, lv)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, VLevel))(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    inp._1 match
      case Lam(_, Impl(_), _) => inp
      case LamLvl(_, _)       => inp
      case _                  => insertPi(inp)

  private def insertUntilName(x: Name, impl: ImplMode, inp: (Tm, VTy, VLevel))(
      implicit ctx: Ctx
  ): (Tm, VTy, VLevel) =
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = force(ty) match
      case VPi(y, Impl(i), a, u1, b, u2) =>
        y match
          case DoBind(yy) if x == yy && i == impl => (tm, ty, lv)
          case _ =>
            val m = newMeta(a, u1)
            val mv = ctx.eval(m)
            go(App(tm, m, Impl(i)), b.inst(mv), u2)
      case VPiLvl(x, b, u) =>
        val m = newLMeta
        val mv = ctx.eval(m)
        go(AppLvl(tm, m), b.inst(mv), u.inst(mv))
      case _ =>
        throw NamedImplicitError(s"no implicit found with name $x")
    go(inp._1, inp._2, inp._3)

  private def insertUntilLevelName(x: Name, inp: (Tm, VTy, VLevel))(implicit
      ctx: Ctx
  ): (Tm, VTy, VLevel) =
    def go(tm: Tm, ty: VTy, lv: VLevel): (Tm, VTy, VLevel) = force(ty) match
      case VPi(y, Impl(i), a, u1, b, u2) =>
        val m = newMeta(a, u1)
        val mv = ctx.eval(m)
        go(App(tm, m, Impl(i)), b.inst(mv), u2)
      case VPiLvl(y, b, u) =>
        y match
          case DoBind(yy) if x == yy => (tm, ty, lv)
          case _ =>
            val m = newLMeta
            val mv = ctx.eval(m)
            go(AppLvl(tm, m), b.inst(mv), u.inst(mv))
      case _ =>
        throw NamedImplicitError(s"no level implicit found with name $x")
    go(inp._1, inp._2, inp._3)

  // elaboration
  private def inferType(ty: RTy)(implicit ctx: Ctx): (Ty, VLevel) =
    val (ety, u, lv) = infer(ty)
    force(u) match
      case VType(l) => (ety, l)
      case _ =>
        val m = ctx.eval(newLMeta)
        val l = VFL(m)
        unify(lv, VFL(m + 1), u, VType(l))
        (ety, l)

  private def inferType(ty: Option[RTy])(implicit
      ctx: Ctx
  ): (Ty, Level, VTy, VLevel) =
    val (ety, lv) = inferType(ty.getOrElse(RHole(None)))
    (ety, ctx.quote(lv), VType(lv), lv.inc)

  private def checkValue(tm: RTm, ty: Option[RTy])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy, VLevel) = ty match
    case Some(ty) =>
      val (ety, lv) = inferType(ty)
      val vty = ctx.eval(ety)
      val etm = check(tm, vty, lv)
      (etm, ety, vty, lv)
    case None =>
      val (etm, vty, lv) = infer(tm)
      (etm, ctx.quote(vty), vty, lv)

  private def namesFromSigma(ty: Val)(implicit ctx: Ctx): List[Name] =
    force(ty) match
      case VSigma(bd @ DoBind(x), ty, u1, b, _) =>
        x :: namesFromSigma(b.inst(VVar(ctx.lvl)))(ctx.bind(bd, ty, u1))
      case VSigma(bd, ty, u1, b, _) =>
        namesFromSigma(b.inst(VVar(ctx.lvl)))(ctx.bind(bd, ty, u1))
      case _ => Nil

  @tailrec
  private def findNameInSigma(
      x: Name,
      tm: Val,
      ty: Val,
      map: Map[Name, Lvl],
      i: Int = 0,
      xs: Set[Name] = Set.empty
  )(implicit ctx: Ctx): (VTy, VLevel, Int) =
    force(ty) match
      case VSigma(DoBind(y), ty, u1, _, _) if x == y => (ty, u1, i)
      case VSigma(y, _, _, c, _) =>
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
  )(implicit ctx: Ctx): (Ctx, Tm => Tm, List[Name]) =
    val (tm, ty, lv) = infer(rtm)
    val vtm = ctx.eval(tm)
    def go(
        ctx: Ctx,
        tm: Tm,
        ns: List[(Name, Option[Name])],
        map: Map[Name, Lvl]
    ): (Ctx, Tm => Tm, List[Name]) = ns match
      case Nil => (ctx, t => t, Nil)
      case (x, oy) :: rest =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then go(ctx, tm, rest, map)
        else
          val (pty, vl, i) = findNameInSigma(y, vtm, ty, map)
          val value = vproj(vtm, Named(Some(y), i))
          val (nctx, builder, ens) = go(
            ctx.define(
              x,
              pty,
              ctx.quote(pty),
              vl,
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
              ),
            x :: ens
          )
    val x = Name("m")
    val qty = ctx.quote(ty)
    val (nctx, builder, ns2) = go(
      ctx.define(x, ty, qty, lv, vtm, tm),
      Var(ix0),
      ns.getOrElse(namesFromSigma(ty).map(x => (x, None))),
      Map.empty
    )
    (nctx, t => Let(x, qty, tm, builder(t)), ns2)

  private def inferExport(
      ns: Option[List[(Name, Option[Name])]],
      hiding: Set[Name]
  )(implicit ctx: Ctx): (Tm, VTy, VLevel) =
    def go(ctx: Ctx, ns: List[(Name, Option[Name])]): Tm = ns match
      case Nil => Prim(PUnit)
      case (x, oy) :: ns =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then go(ctx, ns)
        else
          val (ix, _) = ctx.lookup(y).get
          Pair(Var(ix), go(ctx, ns))
    def goTy(ctx: Ctx, ns: List[(Name, Option[Name])]): (Ty, VLevel) = ns match
      case Nil => (Prim(PUnitType), VLevel.unit)
      case (x, oy) :: ns =>
        val y = oy.getOrElse(x)
        if hiding.contains(y) then
          val (_, Some(ty, lv)) = ctx.lookup(y).get: @unchecked
          goTy(ctx.bind(DoBind(y), ty, lv), ns)
        else
          val (ix, Some(ty, lv)) = ctx.lookup(y).get: @unchecked
          val (body, lv2) = goTy(ctx.bind(DoBind(y), ty, lv), ns)
          (
            Sigma(
              DoBind(x),
              ctx.quote(ty),
              ctx.quote(lv),
              body,
              ctx.quote(lv2)
            ),
            lv max lv2
          )
    val xs = ns.getOrElse(ctx.names.reverse.map(x => (x, None)))
    val tm = go(ctx, xs)
    val (ty, vl) = goTy(ctx, xs)
    val vty = ctx.eval(ty)
    (tm, vty, vl)

  private def inferSig(
      ps: List[(Bind, Option[(Icit, Option[RTy])])],
      ds: List[SigDecl]
  )(implicit ctx: Ctx): (Ty, VTy, VLevel) =
    def createTy(ctx: Ctx, ds: List[SigDecl]): (Ty, Level, VTy, VLevel) =
      ds match
        case Nil =>
          (Prim(PUnitType), LFinLevel(LZ), VType(VLevel.unit), VLevel.unit.inc)
        case (d @ SLet(x, oty)) :: ds =>
          debug(s"infer sig decl $d")
          val dty = ps.foldRight[RTm](oty.getOrElse(RHole(None))) {
            case ((x, None), rty) => RPiLvl(x, rty)
            case ((x, Some((i, oty))), rty) =>
              RPi(x, i, oty.getOrElse(RHole(None)), rty)
          }
          val (ety, elv, ty, lv) =
            inferType(if ps.isEmpty then oty else Some(dty))(ctx)
          val (erty, elv2, rty, rlv) =
            createTy(ctx.bind(DoBind(x), ctx.eval(ety), ctx.eval(elv)), ds)
          val lmax = ctx.eval(elv) max ctx.eval(elv2)
          (
            Sigma(DoBind(x), ety, elv, erty, elv2),
            ctx.quote(lmax),
            VType(lmax),
            lmax.inc
          )
        case (d @ SDef(priv, x, oty, v)) :: ds =>
          debug(s"infer sig decl $d")
          if !priv then throw CannotInferError(d.toString)
          val (dtm, dty) =
            ps.foldRight[(RTm, RTm)]((v, oty.getOrElse(RHole(None)))) {
              case ((x, None), (b, rty)) =>
                (RLamLvl(x, None, b), RPiLvl(x, rty))
              case ((x, Some((i, oty))), (b, rty)) =>
                (
                  RLam(x, RArgIcit(i), None, b),
                  RPi(x, i, oty.getOrElse(RHole(None)), rty)
                )
            }
          val (ev, ety, vty, vl) =
            checkValue(dtm, if ps.isEmpty then oty else Some(dty))(ctx)
          val (erty, elv2, rty, rlv) =
            createTy(ctx.define(x, vty, ety, vl, ctx.eval(ev), ev), ds)
          (Let(x, ety, ev, erty), elv2, rty, rlv)
        case (d @ SOpen(exp, t, xs, hs)) :: ds =>
          debug(s"infer sig decl $d")
          if exp then throw CannotInferError(d.toString)
          val (nctx, builder, _) = inferOpen(t, xs, hs.toSet)(ctx)
          val (erty, elv2, rty, rlv) = createTy(nctx, ds)
          (builder(erty), elv2, rty, rlv)
    val (ety, _, vty, vl) = createTy(ctx, ds)
    (ety, vty, vl)

  private def inferMod(
      ps: List[(Bind, Option[(Icit, Option[RTy])])],
      ds: List[ModDecl]
  )(implicit ctx: Ctx): (Tm, VTy, VLevel) =
    def createCtx(
        ctx: Ctx,
        ds: List[ModDecl]
    ): (Ctx, List[Name], Tm => Tm) = ds match
      case Nil => (ctx, Nil, t => t)
      case (d @ DLet(priv, x, oty, v)) :: ds =>
        debug(s"infer mod decl $d")
        val (dtm, dty) =
          ps.foldRight[(RTm, RTm)]((v, oty.getOrElse(RHole(None)))) {
            case ((x, None), (b, rty)) => (RLamLvl(x, None, b), RPiLvl(x, rty))
            case ((x, Some((i, oty))), (b, rty)) =>
              (
                RLam(x, RArgIcit(i), None, b),
                RPi(x, i, oty.getOrElse(RHole(None)), rty)
              )
          }
        val (ev, ety, vty, vl) =
          checkValue(dtm, if ps.isEmpty then oty else Some(dty))(ctx)
        val (nctx, ns, builder) = createCtx(
          ctx.define(x, vty, ety, vl, ctx.eval(ev), ev),
          ds
        )
        if ns.contains(x) then throw DuplicateModDefError(x.toString)
        (nctx, if priv then ns else x :: ns, t => Let(x, ety, ev, builder(t)))
      case (d @ DOpen(exp, t, xs, hs)) :: ds =>
        debug(s"infer open decl $d")
        val (nctx, builder, ens) = inferOpen(t, xs, hs.toSet)(ctx)
        val (nctx2, ns, builder2) = createCtx(nctx, ds)
        (nctx2, (if exp then ens else Nil) ++ ns, t => builder(builder2(t)))
    val (nctx, ns, builder) = createCtx(ctx, ds)
    val (tm, vt, vl) =
      inferExport(Some(ns.map(x => (x, None))), Set.empty)(nctx)
    (builder(tm), vt, vl)

  private def icitMatch(i1: RArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case RArgNamed(x, impl) =>
      (b, i2) match
        case (DoBind(y), Impl(i2)) => x == y && i2 == impl
        case _                     => false
    case RArgIcit(i) => i == i2

  private def lvlNameMatch(ox: Option[Name], b: Bind): Boolean = ox match
    case None => true
    case Some(x) =>
      b match
        case DoBind(y) => x == y
        case DontBind  => false

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some((_, Some((vty, _)))) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def coe(tm: Tm, ty: VTy, lv: VLevel, tyE: VTy, lvE: VLevel)(implicit
      ctx: Ctx
  ): Tm =
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = ctx.fresh((x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
    )
    def go(
        tm: Tm,
        ty: VTy,
        lv: VLevel,
        tyE: VTy,
        lvE: VLevel
    )(implicit ctx: Ctx): Option[Tm] =
      debug(s"coe ${ctx.pretty(tm)} : ${ctx.pretty(ty)} : ${ctx
          .pretty(lv)} to ${ctx.pretty(tyE)} : ${ctx.pretty(lvE)}")
      (force(ty), force(tyE)) match
        case (VPiLvl(x1, b1, u1), VPiLvl(x2, b2, u2)) =>
          val body = go(
            AppLvl(Wk(tm), LVar(ix0)),
            b1.inst(VFinLevel.vr(ctx.lvl)),
            u1.inst(VFinLevel.vr(ctx.lvl)),
            b2.inst(VFinLevel.vr(ctx.lvl)),
            u2.inst(VFinLevel.vr(ctx.lvl))
          )(ctx.bindLevel(x1))
          body.map(b => LamLvl(x1, b))
        case (VPi(x1, i1, a1, u11, b1, u12), VPi(x2, i2, a2, u21, b2, u22)) =>
          if i1 != i2 then unify(ty, tyE)
          val x = pick(x1, x2)
          val ctx2 = ctx.bind(x, a2, u21)
          go(Var(ix0), a2, u21, a1, u11)(ctx2) match
            case None =>
              val body = go(
                App(Wk(tm), Var(ix0), i1),
                ctx.inst(b1),
                u12,
                ctx.inst(b2),
                u22
              )(ctx2)
              body.map(b => Lam(x1, i1, b))
            case Some(coev0) =>
              val body = go(
                App(Wk(tm), coev0, i1),
                b1.inst(ctx2.eval(coev0)),
                u12,
                ctx.inst(b2),
                u22
              )(ctx2)
              body match
                case None       => Some(Lam(x, i1, App(Wk(tm), coev0, i1)))
                case Some(body) => Some(Lam(x, i1, body))
        case (VSigma(x1, a1, u11, b1, u12), VSigma(x2, a2, u21, b2, u22)) =>
          val fst = go(Proj(tm, Fst), a1, u11, a2, u21)
          val snd = fst match
            case None =>
              go(
                Proj(tm, Snd),
                b1.inst(vproj(ctx.eval(tm), Fst)),
                u12,
                b2.inst(vproj(ctx.eval(tm), Fst)),
                u22
              )
            case Some(fst) =>
              go(
                Proj(tm, Snd),
                b1.inst(vproj(ctx.eval(tm), Fst)),
                u12,
                b2.inst(ctx.eval(fst)),
                u22
              )
          (fst, snd) match
            case (None, None)           => None
            case (Some(fst), None)      => Some(Pair(fst, Proj(tm, Snd)))
            case (None, Some(snd))      => Some(Pair(Proj(tm, Fst), snd))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd))
        case (VVoid(), VVoid()) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VVoid(), VFlex(_, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VVoid(), ty) =>
          val l = newLMeta
          unify(VFL(ctx.eval(l)), lvE)
          Some(
            App(
              App(AppLvl(Prim(PAbsurd), l), ctx.quote(ty), Impl(Unif)),
              tm,
              Expl
            )
          )
        case (VSing(_, _, _), VSing(_, _, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VSing(_, _, _), VFlex(_, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VFlex(_, _), VSing(_, _, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (ty, VSing(l, a, x)) =>
          unify(lv, VFL(l), ty, a)
          unify(ctx.eval(tm), x)
          Some(
            App(
              App(
                AppLvl(Prim(PSingCon), ctx.quote(l)),
                ctx.quote(a),
                Impl(Unif)
              ),
              tm,
              Expl
            )
          )
        case (VSing(l, a, x), ty) =>
          unify(lv, VFL(l), a, ty)
          Some(
            App(
              App(
                App(
                  AppLvl(Prim(PSingElim), ctx.quote(l)),
                  ctx.quote(a),
                  Impl(Unif)
                ),
                ctx.quote(x),
                Impl(Unif)
              ),
              tm,
              Expl
            )
          )
        case (VLift(_, _, _), VLift(_, _, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VFlex(_, _), VLift(_, _, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (VLift(_, _, _), VFlex(_, _)) =>
          unify(lv, lvE, ty, tyE)
          None
        case (ty, VLift(k, l, a)) =>
          unify(lv, VFL(l), ty, a)
          Some(
            App(
              App(
                AppLvl(AppLvl(Prim(PLiftTerm), ctx.quote(k)), ctx.quote(l)),
                ctx.quote(a),
                Impl(Unif)
              ),
              tm,
              Expl
            )
          )
        case (VLift(k, l, a), b) =>
          unify(VFL(l), lvE, a, b)
          Some(
            App(
              App(
                AppLvl(AppLvl(Prim(PLower), ctx.quote(k)), ctx.quote(l)),
                ctx.quote(a),
                Impl(Unif)
              ),
              tm,
              Expl
            )
          )
        case _ =>
          unify(lv, lvE, ty, tyE)
          None
    go(tm, ty, lv, tyE, lvE).getOrElse(tm)

  private def check(tm: RTm, ty: VTy, lv: VLevel)(implicit ctx: Ctx): Tm =
    if !tm.isPos then debug(s"check $tm : ${ctx.pretty(ty)} (${ctx.quote(ty)})")
    (tm, force(ty)) match
      case (RPos(pos, tm), _) => check(tm, ty, lv)(ctx.enter(pos))
      case (RHole(None), _)   => newMeta(ty, lv)
      case (RHole(Some(x)), _) =>
        val t = newMeta(ty, lv)
        holes += x -> HoleEntry(ctx, t, ty, lv)
        t
      case (RLam(x, i, ot, b), VPi(y, i2, t, u1, rt, u2))
          if icitMatch(i, y, i2) =>
        ot.foreach(t0 => {
          val (ety, lvty) = inferType(t0)
          unify(lvty, u1, ctx.eval(ety), t)
        })
        val eb = check(b, ctx.inst(rt), u2)(ctx.bind(x, t, u1))
        Lam(x, i2, eb)
      case (RLamLvl(x, i, b), VPiLvl(y, rty, u)) if lvlNameMatch(i, y) =>
        val v = VFinLevel.vr(ctx.lvl)
        val eb = check(b, rty.inst(v), u.inst(v))(ctx.bindLevel(x))
        LamLvl(x, eb)
      case (RVar(x), VPi(_, Impl(_), _, _, _, _)) if hasMetaType(x) =>
        val Some((ix, Some((varty, lv1)))) = ctx.lookup(x): @unchecked
        unify(lv1, lv, varty, ty)
        Var(ix)
      case (RVar(x), VPiLvl(_, _, _)) if hasMetaType(x) =>
        val Some((ix, Some((varty, lv1)))) = ctx.lookup(x): @unchecked
        unify(lv1, lv, varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl(i), pty, u1, rty, u2)) =>
        val etm = check(tm, ctx.inst(rty), u2)(ctx.bind(x, pty, u1, true))
        Lam(x, Impl(i), etm)
      case (tm, VPiLvl(x, rty, u)) =>
        val v = VFinLevel.vr(ctx.lvl)
        val etm = check(tm, rty.inst(v), u.inst(v))(ctx.bindLevel(x, true))
        LamLvl(x, etm)
      case (RPair(fst, snd), VSigma(_, fty, u1, sty, u2)) =>
        val efst = check(fst, fty, u1)
        val esnd = check(snd, sty.inst(ctx.eval(efst)), u2)
        Pair(efst, esnd)
      case (RLet(x, t, v, b), _) =>
        val (ev, ety, vty, vl) = checkValue(v, t)
        val eb = check(b, ty, lv)(ctx.define(x, vty, ety, vl, ctx.eval(ev), ev))
        Let(x, ety, ev, eb)
      case (ROpen(tm, ns, hiding, b), _) =>
        val (nctx, builder, _) = inferOpen(tm, ns, hiding.toSet)
        builder(check(b, ty, lv)(nctx))
      case (RVar(Name("[]")), VId(l, k, a, b, x, y)) =>
        check(RVar(Name("Refl")), ty, lv)
      case _ =>
        val (etm, ty2, lv2) = insert(infer(tm))
        coe(etm, ty2, lv2, ty, lv)

  private def infer(l: RLevel)(implicit ctx: Ctx): FinLevel =
    if !l.isPos then debug(s"infer $l")
    l match
      case RLPos(pos, l) => infer(l)(ctx.enter(pos))
      case RLVar(x) =>
        ctx.lookup(x) match
          case Some((ix, None)) => LVar(ix)
          case _                => throw UndefVarError(x.toString)
      case RLZ         => LZ
      case RLS(a)      => LS(infer(a))
      case RLMax(a, b) => infer(a) max infer(b)
      case RLHole      => newLMeta

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
  ): (ProjType, VTy, VLevel) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy, VLevel) =
      force(ty) match
        case VSigma(DoBind(y), fstty, u1, _, _) if x == y =>
          (Named(Some(x), ix), fstty, u1)
        case VSigma(y, _, _, sndty, _) =>
          val (clash, newns) = y match
            case DoBind(y) => (ns.contains(y), ns + y)
            case DontBind  => (false, ns)
          go(sndty.inst(projIndex(tm, y, ix, clash)), ix + 1, newns)
        case _ =>
          throw NotSigmaError(s"in named project $x, got ${ctx.pretty(ty)}")
    go(ty, 0, Set.empty)

  private def infer(tm: RTm)(implicit ctx: Ctx): (Tm, VTy, VLevel) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case RPos(pos, tm) => infer(tm)(ctx.enter(pos))
      case RType(l) =>
        val el = infer(l)
        val vl = ctx.eval(el)
        (Type(LFinLevel(el)), VType(VFL(vl + 1)), VFL(vl + 2))
      case RVar(x) =>
        PrimName(x) match
          case Some(name) =>
            val (ty, lv) = getPrimType(name)
            (Prim(name), ty, lv)
          case _ =>
            ctx.lookup(x) match
              case Some((ix, Some((vty, lv)))) =>
                debug(s"var $x : ${ctx.quote(vty)} : ${ctx.quote(lv)}")
                (Var(ix), vty, lv)
              case _ => throw UndefVarError(x.toString)
      case RGlobal(uri) =>
        getGlobal(uri) match
          case Some(e) => (Global(uri), e.vty, e.vl)
          case None    => throw UndefUriError(uri.toString)
      case RLet(x, oty, v, b) =>
        val (ev, ety, vty, vl) = checkValue(v, oty)
        val (eb, rty, vl1) =
          infer(b)(ctx.define(x, vty, ety, vl, ctx.eval(ev), ev))
        (Let(x, ety, ev, eb), rty, vl1)
      case ROpen(tm, ns, hiding, b) =>
        val (nctx, builder, _) = inferOpen(tm, ns, hiding.toSet)
        val (eb, rty, vl) = infer(b)(nctx)
        (builder(eb), rty, vl)
      case RExport(ns, hiding) => inferExport(ns, hiding.toSet)
      case RSig(ps, ds)        => inferSig(ps, ds)
      case RMod(ps, ds)        => inferMod(ps, ds)
      case RPi(x, i, ty, b) =>
        val (ety, l1) = inferType(ty)
        val (eb, l2) = inferType(b)(ctx.bind(x, ctx.eval(ety), l1))
        val u = l1 max l2
        (Pi(x, i, ety, ctx.quote(l1), eb, ctx.quote(l2)), VType(u), u.inc)
      case RSigma(x, ty, b) =>
        val (ety, l1) = inferType(ty)
        val (eb, l2) = inferType(b)(ctx.bind(x, ctx.eval(ety), l1))
        val u = l1 max l2
        (Sigma(x, ety, ctx.quote(l1), eb, ctx.quote(l2)), VType(u), u.inc)
      case RPiLvl(x, b) =>
        val (eb, l) = inferType(b)(ctx.bindLevel(x))
        (PiLvl(x, eb, quote(l)(ctx.lvl + 1)), VType(VOmega), VOmega1)
      case RApp(f, a, i) =>
        val (icit, ef, fty, flv) = i match
          case RArgNamed(x, i) =>
            val (ef, fty, flv) = insertUntilName(x, i, infer(f))
            (Impl(i), ef, fty, flv)
          case RArgIcit(Impl(i)) =>
            val (ef, fty, lv) = insertPi(infer(f), Until(i))
            (Impl(i), ef, fty, lv)
          case RArgIcit(Expl) =>
            val (ef, fty, lv) = insertPi(infer(f))
            (Expl, ef, fty, lv)
        val (pty, u1, rty, u2) = force(fty) match
          case VPi(x, icit2, pty, u1, rty, u2) =>
            if icit != icit2 then throw IcitMismatchError(tm.toString)
            (pty, u1, rty, u2)
          case tty =>
            val l1 = newLMeta
            val u1 = VFL(ctx.eval(l1))
            val l2 = newLMeta
            val u2 = VFL(ctx.eval(l2))
            val pty = ctx.eval(newMeta(VType(u1), u1.inc))
            val x = DoBind(Name("x"))
            val rty =
              CClos[Val](
                ctx.env,
                newMeta(VType(u2), u2.inc)(ctx.bind(x, pty, u1))
              )
            unify(flv, u1 max u2, tty, VPi(x, icit, pty, u1, rty, u2))
            (pty, u1, rty, u2)
        val ea = check(a, pty, u1)
        (App(ef, ea, icit), rty.inst(ctx.eval(ea)), u2)
      case RAppLvl(f, a, i) =>
        val (ef, fty, flv) = i match
          case None       => insertPi(infer(f), NoLvl)
          case Some(name) => insertUntilLevelName(name, infer(f))
        val (rty, clvl) = force(fty) match
          case VPiLvl(x, rty, u) => (rty, u)
          case tty =>
            val x = DoBind(Name("l"))
            val l1 = newLMeta
            val vl1 = ctx.eval(l1)
            val u = VFL(vl1)
            val clvl = ClosLvl(ctx.env, LFinLevel(l1))
            val rty = CClos[VFinLevel](
              ctx.env,
              newMeta(VType(u), u.inc)(ctx.bindLevel(x))
            )
            unify(flv, VOmega, tty, VPiLvl(x, rty, clvl))
            (rty, clvl)
        val ea = infer(a)
        val vea = ctx.eval(ea)
        (AppLvl(ef, ea), rty.inst(vea), clvl.inst(vea))
      case RProj(t, p) =>
        val (et, ty, l1) = insertPi(infer(t))
        (force(ty), p) match
          case (_, RNamed(x)) =>
            val (p, pty, lv) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p), pty, lv)
          case (VSigma(_, fstty, u1, _, _), RFst) => (Proj(et, Fst), fstty, u1)
          case (VSigma(_, _, _, sndty, u2), RSnd) =>
            (Proj(et, Snd), sndty.inst(vproj(ctx.eval(et), Fst)), u2)
          case (tty, RFst) =>
            val u1 = VFL(ctx.eval(newLMeta))
            val u2 = VFL(ctx.eval(newLMeta))
            val pty = ctx.eval(newMeta(VType(u1), u1.inc))
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
          case (tty, RSnd) =>
            val u1 = VFL(ctx.eval(newLMeta))
            val u2 = VFL(ctx.eval(newLMeta))
            val pty = ctx.eval(newMeta(VType(u1), u1.inc))
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
            (Proj(et, Snd), rty.inst(vproj(ctx.eval(et), Fst)), u2)
      case RLam(x, RArgIcit(i), mty, b) =>
        val (pty, lv1) = (mty match
          case Some(ty) =>
            val (ety, lv) = inferType(ty)
            (ctx.eval(ety), lv)
          case None =>
            val u = VFL(ctx.eval(newLMeta))
            val m = newMeta(VType(u), u.inc)
            (ctx.eval(m), u)
        )
        val ctx2 = ctx.bind(x, pty, lv1)
        val (eb, rty, lv2) = insert(infer(b)(ctx2))(ctx2)
        (Lam(x, i, eb), VPi(x, i, pty, lv1, ctx.close(rty), lv2), lv1 max lv2)
      case RLamLvl(x, None, b) =>
        val ctx2 = ctx.bindLevel(x)
        val (eb, rty, u) = insert(infer(b)(ctx2))(ctx2)
        (
          LamLvl(x, eb),
          VPiLvl(x, ctx.close(rty), ClosLvl(ctx.env, quote(u)(ctx.lvl + 1))),
          VOmega
        )
      case RPair(fst, snd) =>
        val (efst, fstty, u1) = infer(fst)
        val (esnd, sndty, u2) = infer(snd)
        (
          Pair(efst, esnd),
          VSigma(DontBind, fstty, u1, CFun(_ => sndty), u2),
          u1 max u2
        )
      case RHole(None) =>
        val l = newLMeta
        val u = VFL(ctx.eval(l))
        val a = ctx.eval(newMeta(VType(u), u.inc))
        val t = newMeta(a, u)
        (t, a, u)
      case RHole(Some(x)) =>
        val l = newLMeta
        val u = VFL(ctx.eval(l))
        val a = ctx.eval(newMeta(VType(u), u.inc))
        val t = newMeta(a, u)
        holes += x -> HoleEntry(ctx, t, a, u)
        (t, a, u)
      case _ => throw CannotInferError(tm.toString)

  private def prettyHoles(implicit ctx0: Ctx): String =
    holes
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty, _) =>
            s"_$x : ${ctx.pretty(vty)} = ${ctx.pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  def elaborate(tm: RTm)(implicit ctx: Ctx): (Tm, Ty, Level) =
    // resetMetas() TODO: zonking
    holes.clear()
    val (etm, vty, lv) = infer(tm)
    debug(etm)
    val ety = ctx.quote(vty)
    debug(ety)
    val el = ctx.quote(lv)
    debug(el)
    if holes.nonEmpty then
      throw HoleError(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)}\n\n${prettyHoles}"
      )
    val ums = unsolvedMetas()
    val ulms = unsolvedLMetas()
    if ums.nonEmpty || ulms.nonEmpty then
      val unsolveduniverselevels =
        s"\nunsolved universe level metas: ${ulms.map(id => s"?l$id").mkString(", ")}"
      throw UnsolvedMetasError(
        s"\n${ctx.pretty(etm)} : ${ctx.pretty(ety)} : ${ctx.pretty(el)}\n${ums
            .map((id, ty) => s"?$id : ${ctx.pretty(ty)}")
            .mkString("\n")}${
            if ulms.isEmpty then "" else unsolveduniverselevels
          }"
      )
    (etm, ety, el)
