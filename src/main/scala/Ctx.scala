import Common.*
import Core.*
import Value.*
import Evaluation.*
import Unification.{unify as unify0}
import Errors.*

import scala.annotation.tailrec

type Inserted = Boolean

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: List[(Name, Lvl, VTy)],
    path: Path,
    pruning: Pruning
):
  def bind(x: Bind, ty: VTy, inserted: Inserted = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => (x, lvl, ty) :: types
      case _                      => types
    Ctx(
      lvl + 1,
      VVar(lvl) :: env,
      newtypes,
      PBind(path, x, ty.quote(lvl)),
      Some(Expl) :: pruning
    )

  def define(x: Name, ty: VTy, qty: Ty, value: Val, qvalue: Tm): Ctx =
    Ctx(
      lvl + 1,
      value :: env,
      (x, lvl, ty) :: types,
      PDefine(path, x, qty, qvalue),
      None :: pruning
    )

  def eval(t: Tm): Val = t.eval(env)
  def quote(v: Val): Tm = v.quote(lvl)

  def under(c: Clos): Val = c(VVar(lvl))
  def close(v: Val): Clos = Clos(env, v.quote(lvl + 1))
  def closeTy(body: Ty): Ty = path.closeTy(body)

  def unify(a: Val, b: Val): Unit = unify0(a, b)(lvl)

  def lookup(x: Name): Option[(Ix, VTy)] =
    @tailrec
    def go(ts: List[(Name, Lvl, VTy)]): Option[(Ix, VTy)] = ts match
      case (y, k, ty) :: _ if x == y => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
      case _                         => None
    go(types)

object Ctx:
  def empty = Ctx(lvl0, Nil, Nil, PHere, Nil)

extension (t: Tm) def evalCtx(implicit ctx: Ctx): Val = ctx.eval(t)

extension (v: Val)
  def quoteCtx(implicit ctx: Ctx): Tm = ctx.quote(v)
  def closeCtx(implicit ctx: Ctx): Clos = ctx.close(v)

extension (c: Clos) def underCtx(implicit ctx: Ctx): Val = ctx.under(c)

def unifyCtx(a: Val, b: Val)(implicit ctx: Ctx): Unit = ctx.unify(a, b)
def lookupCtx(x: Name)(implicit ctx: Ctx): Option[(Ix, VTy)] = ctx.lookup(x)

enum Path:
  case PHere
  case PBind(path: Path, x: Bind, ty: Ty)
  case PDefine(path: Path, x: Name, ty: Ty, tm: Tm)

  def closeTy(b: Ty): Ty = this match
    case PHere               => b
    case PBind(p, x, a)      => p.closeTy(Pi(x, Expl, a, b))
    case PDefine(p, x, a, v) => p.closeTy(Let(x, a, v, b))
export Path.*

def closeTyCtx(body: Ty)(implicit ctx: Ctx): Ty = ctx.closeTy(body)
