import Common.*
import Syntax.*
import Value.*
import Evaluation.{eval as eval0, quote as quote0, inst}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, VTy)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    pos: Pos
):
  def enter(pos: Pos): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy): Ctx =
    val newtypes = x match
      case DoBind(x) => (x, lvl, ty) :: types
      case DontBind  => types
    Ctx(lvl + 1, VVar(lvl) :: env, newtypes, pos)

  def define(x: Name, ty: VTy, value: Val): Ctx =
    Ctx(lvl + 1, value :: env, (x, lvl, ty) :: types, pos)

  def eval(tm: Tm): Val = eval0(tm)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)
  def close(v: Val): Clos = Clos(quote0(v)(lvl + 1))(env)
  def inst(c: Clos): Val = c.inst(VVar(lvl))

  def lookup(x: Name): Option[(Ix, VTy)] =
    @tailrec
    def go(ts: Types): Option[(Ix, VTy)] = ts match
      case (y, k, ty) :: _ if y == x => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
      case Nil                       => None
    go(types)

object Ctx:
  def empty(pos: Pos = (0, 0)) = Ctx(lvl0, Nil, Nil, pos)
