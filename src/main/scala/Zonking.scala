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
    zonk(t)(l + 1, Right(VVar(l)) :: e)
  private def zonkLiftLevel(t: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(t)(l + 1, Left(VFinLevel.vr(l)) :: e)
  private def zonkLift(t: Level)(implicit l: Lvl, e: Env): Level =
    zonk(t)(l + 1, Left(VFinLevel.vr(l)) :: e)

  private def zonk(t: FinLevel)(implicit l: Lvl, e: Env): FinLevel =
    t match
      case LVar(i)    => t
      case LZ         => t
      case LS(a)      => LS(zonk(a))
      case LMax(a, b) => zonk(a) max zonk(b)
      case LMeta(id) =>
        getLMeta(id) match
          case LUnsolved(_, _) => t
          case LSolved(v)      => zonk(v.quote)
  def zonk(t: Level)(implicit l: Lvl, e: Env): Level = t match
    case LOmega       => t
    case LOmega1      => t
    case LFinLevel(l) => LFinLevel(zonk(l))

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
      case AppLvl(fn, arg) =>
        zonkSpine(fn) match
          case Left(v)  => Left(v(eval(arg)))
          case Right(t) => Right(AppLvl(t, zonk(arg)))
      case t => Right(zonk(t))

  def zonk(t: Tm)(implicit l: Lvl, e: Env): Tm = t match
    case Var(_)       => t
    case Global(_, _) => t
    case Type(l)      => Type(zonk(l))
    case Unit         => t
    case UnitType     => t

    case PostponedCheck(id) =>
      getCheck(id) match
        case Checked(tm)              => zonk(tm)
        case Unchecked(_, _, _, _, m) => zonk(Meta(m))

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
    case AppLvl(fn, arg) =>
      zonkSpine(fn) match
        case Left(v)  => zonk(quote(v(eval(arg))))
        case Right(t) => AppLvl(t, zonk(arg))

    case Let(x, ty, value, b) =>
      Let(x, zonk(ty), zonk(value), zonkLift(b))
    case Pi(x, i, ty, u1, b, u2) =>
      Pi(x, i, zonk(ty), zonk(u1), zonkLift(b), zonk(u2))
    case PiLvl(x, b, u) => PiLvl(x, zonkLiftLevel(b), zonkLift(u))
    case LamLvl(x, b)   => LamLvl(x, zonkLiftLevel(b))
    case Lam(x, i, b)   => Lam(x, i, zonkLift(b))

    case Sigma(x, ty, u1, b, u2) =>
      Sigma(x, zonk(ty), zonk(u1), zonkLift(b), zonk(u2))
