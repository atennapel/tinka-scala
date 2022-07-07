import Common.*
import Common.BD.*
import Value.*
import Core.*
import Core.Tm.*
import Metas.*
import Metas.MetaEntry.*
import Evaluation.*
import Errors.*

// inline all solved metas
object Zonking:
  private def zonkLift(l: Lvl, e: Env, t: Tm): Tm =
    zonk(lvlInc(l), VVar(l) :: e, t)

  private def zonkBDs(v: Val, e: Env, sp: BDs): Val = (e, sp) match
    case (Nil, Nil)              => v
    case (_ :: e, Defined :: sp) => zonkBDs(v, e, sp)
    case (w :: e, Bound :: sp)   => vapp(zonkBDs(v, e, sp), w)
    case _                       => throw Impossible()

  private def zonkSpine(l: Lvl, e: Env, t: Tm): Either[Val, Tm] = t match
    case Meta(id) =>
      getMeta(id) match
        case Solved(v, _) => Left(v)
        case Unsolved     => Right(zonk(l, e, t))
    case App(fn, arg) =>
      zonkSpine(l, e, fn) match
        case Left(v)  => Left(vapp(v, eval(e, arg)))
        case Right(t) => Right(App(t, zonk(l, e, arg)))
    case t => Right(zonk(l, e, t))

  def zonk(l: Lvl, e: Env, t: Tm): Tm = t match
    case Var(ix)      => t
    case Global(name) => t
    case Type         => t

    case Meta(id) =>
      getMeta(id) match
        case Unsolved     => t
        case Solved(_, c) => zonk(l, e, c)
    case InsertedMeta(id, sp) => zonk(l, e, quote(l, zonkBDs(vmeta(id), e, sp)))

    case App(fn, arg) =>
      zonkSpine(l, e, fn) match
        case Left(v)  => zonk(l, e, quote(l, vapp(v, eval(e, arg))))
        case Right(t) => App(t, zonk(l, e, arg))

    case Let(x, ty, value, b) =>
      Let(x, zonk(l, e, ty), zonk(l, e, value), zonkLift(l, e, b))
    case Pi(x, ty, b) => Pi(x, zonk(l, e, ty), zonkLift(l, e, b))
    case Lam(x, b)    => Lam(x, zonkLift(l, e, b))

  def zonk(t: Tm): Tm = zonk(initialLvl, List.empty, t)
