import Common.*
import Common.BD.*
import Value.*
import scala.util.parsing.input.{Position, NoPosition}
import Evaluation.{eval as veval, quote as vquote}
import Core.*
import scala.annotation.tailrec
import Pretty.{pretty as pretty0}

final case class Ctx(
    val env: Env,
    val lvl: Lvl,
    val types: List[(Name, Val)],
    val bds: BDs,
    val pos: Position
):
  def names: List[Name] = types.map(_._1)

  def enter(pos: Position): Ctx = copy(pos = pos)

  def bind(x: Name, ty: Val): Ctx =
    copy(
      env = VVar(lvl) :: env,
      lvl = lvlInc(lvl),
      types = (x, ty) :: types,
      bds = Bound :: bds
    )
  def define(x: Name, ty: Val, value: Val): Ctx =
    copy(
      env = value :: env,
      lvl = lvlInc(lvl),
      types = (x, ty) :: types,
      bds = Defined :: bds
    )

  def closeVal(v: Val): Clos = Clos(env, vquote(lvlInc(lvl), v))

  def eval(tm: Tm): Val = veval(env, tm)
  def quote(v: Val): Tm = vquote(lvl, v)

  def pretty(tm: Tm): String = pretty0(tm, names)
  def pretty(v: Val): String = pretty0(quote(v), names)

  def lookup(name: Name): Option[(Ix, Val)] =
    @tailrec
    def go(ts: List[(Name, Val)], ix: Ix): Option[(Ix, Val)] = ts match
      case List()                    => None
      case (x, ty) :: _ if x == name => Some((ix, ty))
      case _ :: rest                 => go(rest, ixInc(ix))
    go(types, initialIx)

object Ctx:
  def empty(pos: Position = NoPosition): Ctx =
    Ctx(List.empty, initialLvl, List.empty, List.empty, pos)
