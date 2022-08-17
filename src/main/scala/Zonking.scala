import Common.*
import Value.*
import Core.*
import Metas.*
import Evaluation.*
import Errors.*
import Debug.*

// inline all solved metas
object Zonking:
  private def zonkLift(t: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(t)(l + 1, VVar(l) :: e)

  private def zonkSpine(t: Tm)(implicit l: Lvl, e: Env): Either[Val, Tm] =
    t match
      case Meta(id) =>
        getMeta(id) match
          case Solved(v, _, _) => Left(v)
          case Unsolved(_, _)  => Right(zonk(t))
      case App(fn, arg, i) =>
        zonkSpine(fn) match
          case Left(v)  => Left(v(eval(arg), i))
          case Right(t) => Right(App(t, zonk(arg), i))
      case t => Right(zonk(t))

  def zonk(t: Tm)(implicit l: Lvl, e: Env): Tm = t match
    case Var(ix)  => t
    case Type     => t
    case Unit     => t
    case UnitType => t

    case PostponedCheck(id) =>
      getCheck(id) match
        case Checked(tm)           => zonk(tm)
        case Unchecked(_, _, _, m) => zonk(Meta(m))

    case Meta(id) =>
      getMeta(id) match
        case Unsolved(_, _)  => t
        case Solved(_, c, _) => zonk(c)(lvl0, Nil)
    case AppPruning(t, sp) => zonk(quote(vappPruning(t.eval, sp)))

    case Pair(fst, snd) => Pair(zonk(fst), zonk(snd))
    case Proj(tm, proj) => Proj(zonk(tm), proj)
    case App(fn, arg, i) =>
      zonkSpine(fn) match
        case Left(v)  => zonk(quote(v(eval(arg), i)))
        case Right(t) => App(t, zonk(arg), i)

    case Let(x, ty, value, b) =>
      Let(x, zonk(ty), zonk(value), zonkLift(b))
    case Pi(x, i, ty, b) => Pi(x, i, zonk(ty), zonkLift(b))
    case Lam(x, i, b)    => Lam(x, i, zonkLift(b))

    case Sigma(x, ty, b) => Sigma(x, zonk(ty), zonkLift(b))
