import Common.*
import Core.*
import Value.*
import Evaluation.*
import Zonking.{zonk as zonk0}
import Errors.*
import Pretty.{pretty as pretty0}

import scala.annotation.tailrec
import scala.annotation.targetName

type Inserted = Boolean

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    path: Path,
    pruning: Pruning,
    pos: Pos
):
  def enter(p: Pos): Ctx = copy(pos = p)

  def bind(x: Bind, ty: VTy, lv: VLevel, inserted: Inserted = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => TVar(types, x, lvl, ty, lv)
      case _                      => types
    Ctx(
      lvl + 1,
      Right(VVar(lvl)) :: env,
      newtypes,
      PBind(path, x, ty.quote(lvl), lv.quote(lvl)),
      Some(Expl) :: pruning,
      pos
    )

  def define(
      x: Name,
      ty: VTy,
      qty: Ty,
      lv: VLevel,
      value: Val,
      qvalue: Tm
  ): Ctx =
    Ctx(
      lvl + 1,
      Right(value) :: env,
      TVar(types, x, lvl, ty, lv),
      PDefine(path, x, qty, lv.quote(lvl), qvalue),
      None :: pruning,
      pos
    )

  def bindLevel(x: Bind, inserted: Inserted = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => TLVar(types, x, lvl)
      case _                      => types
    Ctx(
      lvl + 1,
      Left(VFinLevel.vr(lvl)) :: env,
      newtypes,
      PBindLevel(path, x),
      Some(Impl) :: pruning,
      pos
    )

  def eval(t: Tm): Val = t.eval(env)
  def eval(l: Level): VLevel = l.eval(env)
  def eval(l: FinLevel): VFinLevel = l.eval(env)
  def quote(v: Val): Tm = v.quote(lvl)
  def quote(l: VLevel): Level = l.quote(lvl)
  def quote(l: VFinLevel): FinLevel = l.quote(lvl)
  def zonk(t: Tm): Tm = zonk0(t)(lvl, env)
  def zonk(t: Level): Level = zonk0(t)(lvl, env)
  def pretty(t: Tm): String = pretty0(t)(names)
  def pretty(t: Level): String = pretty0(t)(names)

  def under(c: Clos[Val]): Val = c(VVar(lvl))
  def underLvl(c: Clos[VFinLevel]): Val = c(VFinLevel.vr(lvl))
  def close[A](v: Val): Clos[A] = CClos(env, v.quote(lvl + 1))
  def closeTy(body: Ty, lv: Level): Ty = path.closeTy(body, lv)
  def closeTm(body: Tm): Tm = path.closeTm(body)
  def closeVTy(ty: VTy, lv: Level): VTy = closeTy(quote(ty), lv).eval(Nil)

  def lookup(x: Name): Option[(Ix, Option[(VTy, VLevel)])] =
    @tailrec
    def go(ts: Types): Option[(Ix, Option[(VTy, VLevel)])] =
      ts match
        case TVar(_, y, k, ty, lv) if x == y =>
          Some((k.toIx(lvl), Some((ty, lv))))
        case TLVar(_, y, k) if x == y => Some((k.toIx(lvl), None))
        case TVar(ts, _, _, _, _)     => go(ts)
        case TLVar(ts, _, _)          => go(ts)
        case _                        => None
    go(types)

  def names: List[Name] = path.names

  def levelVars: Set[Lvl] =
    def go(i: Int, p: Path): Set[Lvl] = p match
      case PBindLevel(p, _)       => go(i + 1, p) + mkLvl(lvl.expose - i - 1)
      case PBind(p, _, _, _)      => go(i + 1, p)
      case PDefine(p, _, _, _, _) => go(i + 1, p)
      case PHere                  => Set.empty
    go(0, path)

  def throwElab(err: Pos => ElabError): Nothing = throw err(pos)

  def prettyLocal: String =
    def go(p: Path): List[String] = p match
      case PHere                   => Nil
      case PBind(p, x, ty, _)      => s"$x : ${pretty0(ty)(p.names)}" :: go(p)
      case PBindLevel(p, x)        => s"level $x" :: go(p)
      case PDefine(p, x, ty, _, _) => s"$x : ${pretty0(ty)(p.names)}" :: go(p)
    go(path).mkString("\n")

object Ctx:
  def empty: Ctx = empty((1, 1))
  def empty(pos: Pos): Ctx = Ctx(lvl0, Nil, TEmpty, PHere, Nil, pos)

extension (t: Tm)
  def evalCtx(implicit ctx: Ctx): Val = ctx.eval(t)
  def closeTyCtx(lv: Level)(implicit ctx: Ctx): Ty = ctx.closeTy(t, lv)
  def closeTmCtx(implicit ctx: Ctx): Tm = ctx.closeTm(t)
  def zonkCtx(implicit ctx: Ctx): Tm = ctx.zonk(t)
  def prettyCtx(implicit ctx: Ctx): String = ctx.pretty(t.zonkCtx)

extension (l: Level)
  def evalCtx(implicit ctx: Ctx): VLevel = ctx.eval(l)
  def zonkCtx(implicit ctx: Ctx): Level = ctx.zonk(l)
  def prettyCtx(implicit ctx: Ctx): String = ctx.pretty(l.zonkCtx)

extension (l: FinLevel) def evalCtx(implicit ctx: Ctx): VFinLevel = ctx.eval(l)

extension (v: Val)
  def quoteCtx(implicit ctx: Ctx): Tm = ctx.quote(v)
  def closeCtx[A](implicit ctx: Ctx): Clos[A] = ctx.close(v)
  def closeVTyCtx(lv: Level)(implicit ctx: Ctx): VTy = ctx.closeVTy(v, lv)
  def prettyCtx(implicit ctx: Ctx): String = v.quoteCtx.zonkCtx.prettyCtx

extension (l: VLevel)
  def quoteCtx(implicit ctx: Ctx): Level = ctx.quote(l)
  def prettyCtx(implicit ctx: Ctx): String = l.quoteCtx.zonkCtx.prettyCtx

extension (l: VFinLevel)
  def quoteCtx(implicit ctx: Ctx): FinLevel = ctx.quote(l)

extension (c: Clos[Val]) def underCtx(implicit ctx: Ctx): Val = ctx.under(c)
extension (c: Clos[VFinLevel])
  @targetName("underCtxVFinLevel")
  def underCtx(implicit ctx: Ctx): Val = ctx.underLvl(c)

def lookupCtx(x: Name)(implicit ctx: Ctx): Option[(Ix, Option[(VTy, VLevel)])] =
  ctx.lookup(x)

def throwCtx(err: Pos => ElabError)(implicit ctx: Ctx): Nothing =
  ctx.throwElab(err)

enum Types:
  case TEmpty
  case TVar(ts: Types, x: Name, lvl: Lvl, ty: VTy, lv: VLevel)
  case TLVar(ts: Types, x: Name, lvl: Lvl)
export Types.*

enum Path:
  case PHere
  case PBind(path: Path, x: Bind, ty: Ty, lv: Level)
  case PBindLevel(path: Path, x: Bind)
  case PDefine(path: Path, x: Name, ty: Ty, lv: Level, tm: Tm)

  def closeTy(b: Ty, l: Level): Ty =
    def goLevels(p: Path): List[(Bind, Option[Level])] = p match
      case PHere                  => Nil
      case PBind(p, x, _, lv)     => (x, Some(lv)) :: goLevels(p)
      case PBindLevel(p, x)       => (x, None) :: goLevels(p)
      case PDefine(p, _, _, _, _) => goLevels(p)
    @tailrec
    def go(p: Path, b: Ty, l: List[Level]): Ty =
      (p, l) match
        case (PHere, Nil) => b
        case (PBind(p, x, a, lv), l :: lvls) =>
          go(p, Pi(x, Expl, a, lv, b, l), lvls)
        case (PBindLevel(p, x), l :: lvls)  => go(p, PiLvl(x, b, l), lvls)
        case (PDefine(p, x, a, _, v), lvls) => go(p, Let(x, a, v, b), lvls)
        case _                              => throw Impossible
    val plvls = goLevels(this)
    val (_, lvls) = plvls.foldLeft((List(l), List.empty[Level])) {
      case ((prevs, res), (x, o)) =>
        val prev = if o.isDefined then prevs.head.shift(-1) else prevs.head
        val next = prev max o.getOrElse(LOmega)
        (next :: prevs, prev :: res)
    }
    go(this, b, lvls.reverse)

  def closeTm(b: Tm): Tm = this match
    case PHere                  => b
    case PBind(p, x, _, _)      => p.closeTm(Lam(x, Expl, b))
    case PBindLevel(p, x)       => p.closeTm(LamLvl(x, b))
    case PDefine(p, x, a, _, v) => p.closeTm(Let(x, a, v, b))

  def names: List[Name] = this match
    case PHere                  => Nil
    case PBind(p, x, _, _)      => x.toName :: p.names
    case PBindLevel(p, x)       => x.toName :: p.names
    case PDefine(p, x, _, _, _) => x :: p.names
export Path.*
