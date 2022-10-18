import Common.*
import Syntax.*
import Value.*
import Evaluation.{eval as eval0, quote as quote0, inst}
import Pretty.{pretty as pretty0}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, VTy)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    path: Path,
    pruning: Pruning,
    pos: Pos
):
  def names: List[Name] = path.names

  def enter(pos: Pos): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy, inserted: Boolean = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => (x, lvl, ty) :: types
      case _                      => types
    Ctx(
      lvl + 1,
      VVar(lvl) :: env,
      newtypes,
      PBind(path, x, quote(ty)),
      Some(Expl) :: pruning,
      pos
    )

  def define(x: Name, ty: VTy, qty: Ty, value: Val, qvalue: Tm): Ctx =
    Ctx(
      lvl + 1,
      value :: env,
      (x, lvl, ty) :: types,
      PDefine(path, x, qty, qvalue),
      None :: pruning,
      pos
    )

  def eval(tm: Tm): Val = eval0(tm)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)
  def close(v: Val): Clos = Clos(quote0(v)(lvl + 1))(env)
  def inst(c: Clos): Val = c.inst(VVar(lvl))

  def pretty(tm: Tm): String = pretty0(tm)(names)
  def pretty(v: Val): String = pretty(quote(v))

  def closeTy(b: Ty): Ty = path.closeTy(b)
  def closeTy(b: VTy): Ty = closeTy(quote(b))
  def closeTm(b: Tm): Tm = path.closeTm(b)
  def closeTm(b: Val): Tm = closeTm(quote(b))

  def lookup(x: Name): Option[(Ix, VTy)] =
    @tailrec
    def go(ts: Types): Option[(Ix, VTy)] = ts match
      case (y, k, ty) :: _ if y == x => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
      case Nil                       => None
    go(types)

  def prettyLocals: String =
    def go(p: Path): List[String] = p match
      case PHere                => Nil
      case PBind(p, x, ty)      => s"$x : ${pretty0(ty)(p.names)}" :: go(p)
      case PDefine(p, x, ty, _) => s"$x : ${pretty0(ty)(p.names)}" :: go(p)
    go(path).mkString("\n")

object Ctx:
  def empty(pos: Pos = (0, 0)) = Ctx(lvl0, Nil, Nil, PHere, Nil, pos)

enum Path:
  case PHere
  case PBind(path: Path, x: Bind, ty: Ty)
  case PDefine(path: Path, x: Name, ty: Ty, tm: Tm)

  def closeTy(b: Ty): Ty = this match
    case PHere               => b
    case PBind(p, x, a)      => p.closeTy(Pi(x, Expl, a, b))
    case PDefine(p, x, a, v) => p.closeTy(Let(x, a, v, b))

  def closeTm(b: Tm): Tm = this match
    case PHere               => b
    case PBind(p, x, _)      => p.closeTm(Lam(x, Expl, b))
    case PDefine(p, x, a, v) => p.closeTm(Let(x, a, v, b))

  def names: List[Name] = this match
    case PHere               => Nil
    case PBind(p, x, _)      => x.toName :: p.names
    case PDefine(p, x, _, _) => x :: p.names
export Path.*
