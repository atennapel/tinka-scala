import Common.*
import Common.BD.*
import Value.*
import Value.Clos.*
import Evaluation.{eval as veval, quote as vquote, vinst}
import Core.*
import Pretty.{pretty as pretty0}
import Zonking.{zonk as zonk0}
import scala.annotation.tailrec
import scala.util.parsing.input.{Position, NoPosition}

final case class Ctx(
    val env: Env,
    val lvl: Lvl,
    val types: List[(Name, Boolean, Val)],
    val bds: BDs,
    val pos: Position
):
  def names: List[Name] = types.map(_._1)

  def enter(pos: Position): Ctx = copy(pos = pos)

  def bind(x: Name, i: Icit, ty: Val, inserted: Boolean = false): Ctx =
    copy(
      env = VVar(lvl) :: env,
      lvl = lvlInc(lvl),
      types = (x, inserted, ty) :: types,
      bds = Bound(i) :: bds
    )
  def define(x: Name, ty: Val, value: Val): Ctx =
    copy(
      env = value :: env,
      lvl = lvlInc(lvl),
      types = (x, false, ty) :: types,
      bds = Defined :: bds
    )

  def clos(tm: Tm): Clos = ClosEnv(env, tm)
  def closeVal(v: Val): Clos = ClosEnv(env, vquote(lvlInc(lvl), v))

  def eval(tm: Tm): Val = veval(env, tm)
  def quote(v: Val): Tm = vquote(lvl, v)
  def inst(c: Clos): Val = vinst(c, VVar(lvl))

  def pretty(tm: Tm): String = pretty0(tm, names)
  def pretty(v: Val): String = pretty0(quote(v), names)

  def zonk(tm: Tm): Tm = zonk0(lvl, env, tm)

  def lookup(name: Name): Option[(Ix, Val)] =
    @tailrec
    def go(ts: List[(Name, Boolean, Val)], ix: Ix): Option[(Ix, Val)] = ts match
      case Nil                          => None
      case (x, _, ty) :: _ if x == name => Some((ix, ty))
      case _ :: rest                    => go(rest, ixInc(ix))
    go(types, initialIx)

  def show: String =
    types.map { case (x, _, ty) => s"$x : ${pretty(ty)}" }.mkString("\n")

object Ctx:
  def empty(pos: Position = NoPosition): Ctx =
    Ctx(Nil, initialLvl, Nil, Nil, pos)
