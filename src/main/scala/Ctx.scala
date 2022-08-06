import Common.*
import Core.*
import Value.*
import Evaluation.*
import Unification.{unify as unify0}
import Errors.*
import scala.annotation.tailrec

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: List[(Name, Lvl, VTy)]
):
  def names: List[Name] = types.map(_._1)

  def bind(x: Bind, ty: VTy): Ctx =
    val newtypes = x match
      case Bound(x) => (x, lvl, ty) :: types
      case DontBind => types
    copy(lvl + 1, VVar(lvl) :: env, newtypes)
  def define(x: Name, ty: VTy, value: Val): Ctx =
    copy(lvl + 1, value :: env, (x, lvl, ty) :: types)

  def eval(t: Tm): Val = t.eval(env)
  def quote(v: Val): Tm = v.quote(lvl)

  def under(c: Clos): Val = c(VVar(lvl))
  def close(v: Val): Clos = Clos(env, v.quote(lvl + 1))

  def unify(a: Val, b: Val): Unit = unify0(a, b)(lvl)

  def lookup(x: Name): Option[(Ix, VTy)] =
    @tailrec
    def go(ts: List[(Name, Lvl, VTy)]): Option[(Ix, VTy)] = ts match
      case (y, k, ty) :: _ if x == y => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
      case _                         => None
    go(types)

object Ctx:
  def empty = Ctx(lvl0, Nil, Nil)

extension (t: Tm) def evalCtx(implicit ctx: Ctx): Val = ctx.eval(t)

extension (v: Val)
  def quoteCtx(implicit ctx: Ctx): Tm = ctx.quote(v)
  def closeCtx(implicit ctx: Ctx): Clos = ctx.close(v)

extension (c: Clos) def underCtx(implicit ctx: Ctx): Val = ctx.under(c)

def unifyCtx(a: Val, b: Val)(implicit ctx: Ctx): Unit = ctx.unify(a, b)
def lookupCtx(x: Name)(implicit ctx: Ctx): Option[(Ix, VTy)] = ctx.lookup(x)
