import Common.{fresh as fresh0, *}
import Syntax.*
import Value.*
import Evaluation.{eval as eval0, quote as quote0, inst}
import Pretty.{pretty as pretty0}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, Option[(VTy, VLevel)])]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    path: Path,
    pruning: Pruning,
    levelPruning: List[Boolean],
    pos: Pos
):
  def names: List[Name] = path.names

  def fresh(x: Name) = fresh0(x)(names)
  def fresh(x: Bind) = fresh0(x)(names)

  def enter(pos: Pos): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy, lv: VLevel, inserted: Boolean = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => (x, lvl, Some((ty, lv))) :: types
      case _                      => types
    Ctx(
      lvl + 1,
      EVal(env, VVar(lvl)),
      newtypes,
      PBind(path, x, quote(ty), quote(lv)),
      Some(Expl) :: pruning,
      false :: levelPruning,
      pos
    )

  def bindLevel(x: Bind, inserted: Boolean = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => (x, lvl, None) :: types
      case _                      => types
    Ctx(
      lvl + 1,
      ELevel(env, VFinLevel.vr(lvl)),
      newtypes,
      PBindLevel(path, x),
      Some(Expl) :: pruning,
      true :: levelPruning,
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
      EVal(env, value),
      (x, lvl, Some((ty, lv))) :: types,
      PDefine(path, x, qty, quote0(lv)(lvl), qvalue),
      None :: pruning,
      false :: levelPruning,
      pos
    )

  def eval(tm: Tm): Val = eval0(tm)(env)
  def eval(tm: Level): VLevel = eval0(tm)(env)
  def eval(tm: FinLevel): VFinLevel = eval0(tm)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)
  def quote(v: VLevel): Level = quote0(v)(lvl)
  def quote(v: VFinLevel): FinLevel = quote0(v)(lvl)
  def close[A](v: Val): Clos[A] = Clos(quote0(v)(lvl + 1))(env)
  def inst(c: Clos[Val]): Val = c.inst(VVar(lvl))

  def pretty(tm: Tm): String = pretty0(tm)(names)
  def pretty(tm: Level): String = pretty0(tm)(names)
  def pretty(tm: FinLevel): String = pretty0(tm)(names)
  def pretty(v: Val): String = pretty(quote(v))
  def pretty(v: VLevel): String = pretty(quote(v))
  def pretty(v: VFinLevel): String = pretty(quote(v))

  def closeTy(b: Ty, lv: Level): Ty = path.closeTy(b, lv)
  def closeVTy(b: VTy, lv: Level): VTy = eval0(closeTy(quote(b), lv))(EEmpty)
  def closeTm(b: Tm): Tm = path.closeTm(b)
  def closeTm(b: Val): Tm = closeTm(quote(b))

  def lookup(x: Name): Option[(Ix, Option[(VTy, VLevel)])] =
    @tailrec
    def go(ts: Types): Option[(Ix, Option[(VTy, VLevel)])] = ts match
      case (y, k, ty) :: _ if y == x => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
      case Nil                       => None
    go(types)

  def prettyLocals: String =
    def go(p: Path): List[String] = p match
      case PHere              => Nil
      case PBind(p, x, ty, _) => s"$x : ${pretty0(ty)(p.names)}" :: go(p)
      case PBindLevel(p, x)   => s"<$x>" :: go(p)
      case PDefine(p, x, ty, _, v) =>
        s"$x : ${pretty0(ty)(p.names)} = ${pretty0(v)(p.names)}" :: go(p)
    go(path).mkString("\n")

object Ctx:
  def empty(pos: Pos = (0, 0)) = Ctx(lvl0, EEmpty, Nil, PHere, Nil, Nil, pos)

enum Path:
  case PHere
  case PBind(path: Path, x: Bind, ty: Ty, lv: Level)
  case PBindLevel(path: Path, x: Bind)
  case PDefine(path: Path, x: Name, ty: Ty, lv: Level, tm: Tm)

  // TODO: improve closeTy
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
        case _                              => impossible()
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
