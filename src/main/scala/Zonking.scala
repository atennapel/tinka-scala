import Common.*
import Syntax.*
import Value.*
import Metas.*
import Evaluation.*
import Errors.*
import Debug.*

object Zonking:
  private type VT = Either[Val, Tm]

  private def quoteVT(t: VT)(implicit l: Lvl): Tm =
    t.fold(v => quote(v, UnfoldMetas), t => t)

  def zonk(t: FinLevel)(implicit l: Lvl, e: Env): FinLevel = nf(t)
  def zonk(t: Level)(implicit l: Lvl, e: Env): Level = nf(t)

  private def zonkLift(tm: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(tm)(l + 1, EVal(e, VVar(l)))
  private def zonkLift(tm: Level)(implicit l: Lvl, e: Env): Level =
    zonk(tm)(l + 1, ELevel(e, VFinLevel.vr(l)))
  private def zonkLiftLevel(tm: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(tm)(l + 1, ELevel(e, VFinLevel.vr(l)))

  private def app(f: VT, a: Val, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, a, i)), t => Right(App(t, quote(a), i)))

  private def app(f: VT, a: Tm, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, eval(a), i)), t => Right(App(t, zonk(a), i)))

  private def appLvl(f: VT, a: VFinLevel)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, a)), t => Right(AppLvl(t, quote(a))))

  private def proj(t: VT, p: ProjType): VT =
    t.fold(v => Left(vproj(v, p)), t => Right(Proj(t, p)))

  private def meta(id: MetaId)(implicit l: Lvl, e: Env): VT =
    getMeta(id) match
      case Solved(v, _, _) => Left(v)
      case _               => Right(Meta(id))

  private def appPruning(t: Tm, sp: Pruning)(implicit l: Lvl, e: Env): VT =
    zonkSp(t).fold(v => Left(vappPruning(v, sp)), t => Right(AppPruning(t, sp)))

  private def zonkSp(t: Tm)(implicit l: Lvl, e: Env): VT =
    t match
      case AppPruning(t, sp) => appPruning(t, sp)
      case Meta(id)          => meta(id)
      case App(f, a, i)      => app(zonkSp(f), a, i)
      case Proj(t, p)        => proj(zonkSp(t), p)
      case AppLvl(f, a)      => appLvl(zonkSp(f), eval(a))
      case t                 => Right(t)

  def zonk(tm: Tm)(implicit l: Lvl, e: Env): Tm = tm match
    case Type(lvl)   => Type(zonk(lvl))
    case Var(_)      => tm
    case Global(_)   => tm
    case Prim(_)     => tm
    case LabelLit(_) => tm

    case Let(x, t, v, b) => Let(x, zonk(t), zonk(v), zonkLift(b))

    case Lam(x, i, b) => Lam(x, i, zonkLift(b))
    case Pi(x, i, t, u1, b, u2) =>
      Pi(x, i, zonk(t), zonk(u1), zonkLift(b), zonk(u2))

    case LamLvl(x, b)   => LamLvl(x, zonkLiftLevel(b))
    case PiLvl(x, b, u) => PiLvl(x, zonkLiftLevel(b), zonkLift(u))

    case Pair(fst, snd) => Pair(zonk(fst), zonk(snd))
    case Sigma(x, t, u1, b, u2) =>
      Sigma(x, zonk(t), zonk(u1), zonkLift(b), zonk(u2))

    case App(f, a, i) => quoteVT(app(zonkSp(f), a, i))
    case AppLvl(f, a) => quoteVT(appLvl(zonkSp(f), eval(a)))
    case Proj(t, p)   => quoteVT(proj(zonkSp(t), p))

    case Wk(t) => Wk(zonk(t)(l - 1, e.tail))

    case Meta(id)          => quoteVT(meta(id))
    case AppPruning(t, sp) => quoteVT(appPruning(t, sp))
