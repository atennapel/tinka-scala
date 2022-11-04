import Common.*
import Syntax.*
import Value.*
import Metas.*

object Evaluation:
  extension (c: Clos[Val])
    def apply(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(EVal(env, v))
      case CFun(fn)       => fn(v)

  extension (c: Clos[VFinLevel])
    def apply(v: VFinLevel): Val = c match
      case CClos(env, tm) => eval(tm)(ELevel(env, v))
      case CFun(fn)       => fn(v)

  extension (c: ClosLvl)
    def apply(v: VFinLevel): VLevel = eval(c.tm)(ELevel(c.env, v))

  // evaluation
  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, b)  => b(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg, icit))
    case VFlex(hd, sp)  => VFlex(hd, SApp(sp, arg, icit))
    case _              => impossible()

  def vapp(fn: Val, arg: VFinLevel): Val = fn match
    case VLamLvl(_, b)  => b(arg)
    case VRigid(hd, sp) => VRigid(hd, SAppLvl(sp, arg))
    case VFlex(hd, sp)  => VFlex(hd, SAppLvl(sp, arg))
    case _              => impossible()

  def vproj(tm: Val, proj: ProjType): Val = tm match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp) => VRigid(hd, SProj(sp, proj))
    case VFlex(hd, sp)  => VFlex(hd, SProj(sp, proj))
    case _              => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId             => v
    case SApp(sp, a, i)  => vapp(vspine(v, sp), a, i)
    case SAppLvl(sp, a)  => vapp(vspine(v, sp), a)
    case SProj(sp, proj) => vproj(vspine(v, sp), proj)

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_)     => VMeta(id)

  def vlmeta(id: LMetaId): VFinLevel = getLMeta(id) match
    case LSolved(v)      => v
    case LUnsolved(_, _) => VFinLevel.meta(id)

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (EEmpty, Nil)                 => v
      case (EVal(env, t), Some(i) :: pr) => vapp(vappPruning(v, pr)(env), t, i)
      case (ELevel(env, t), Some(_) :: pr) => vapp(vappPruning(v, pr)(env), t)
      case (EVal(env, _), None :: pr)      => vappPruning(v, pr)(env)
      case (ELevel(env, _), None :: pr)    => vappPruning(v, pr)(env)
      case _                               => impossible()

  def eval(l: FinLevel)(implicit env: Env): VFinLevel = l match
    case LVar(ix)   => env(ix).swap.toOption.get
    case LZ         => VFinLevel.unit
    case LS(a)      => eval(a) + 1
    case LMax(a, b) => eval(a) max eval(b)
    case LMeta(id)  => vlmeta(id)

  def eval(l: Level)(implicit env: Env): VLevel = l match
    case LOmega       => VOmega
    case LOmega1      => VOmega1
    case LFinLevel(l) => VFL(eval(l))

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Type(l)         => VType(eval(l))
    case Var(ix)         => env(ix).toOption.get
    case Let(_, _, v, b) => eval(b)(EVal(env, eval(v)))

    case Lam(x, i, b) => VLam(x, i, Clos(b))
    case App(f, a, i) => vapp(eval(f), eval(a), i)
    case Pi(x, i, t, u1, b, u2) =>
      VPi(x, i, eval(t), eval(u1), Clos(b), eval(u2))

    case LamLvl(x, body)   => VLamLvl(x, CClos(env, body))
    case AppLvl(fn, arg)   => vapp(eval(fn), eval(arg))
    case PiLvl(x, body, u) => VPiLvl(x, CClos(env, body), ClosLvl(env, u))

    case Pair(fst, snd) => VPair(eval(fst), eval(snd))
    case Proj(tm, proj) => vproj(eval(tm), proj)
    case Sigma(x, t, u1, b, u2) =>
      VSigma(x, eval(t), eval(u1), Clos(b), eval(u2))

    case UnitType  => VUnitType
    case UnitValue => VUnitValue

    case Wk(tm) => eval(tm)(env.tail)

    case Meta(id)           => vmeta(id)
    case AppPruning(tm, pr) => vappPruning(eval(tm), pr)

  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  // forcing
  def force(l: VFinLevel): VFinLevel =
    l.metas
      .map { (id, n) =>
        getLMeta(lmetaId(id)) match
          case LUnsolved(_, _) => vlmeta(lmetaId(id)) + n
          case LSolved(v)      => force(v + n)
      }
      .foldRight(VFinLevel(l.k, l.vars))(_ max _)

  def force(v: VLevel): VLevel = v match
    case VFL(l) => VFL(force(l))
    case _      => v

  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _, _) => force(vspine(v, sp))
        case Unsolved(_)     => v
    case _ => v

  // quoting
  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SAppLvl(fn, arg) => AppLvl(quote(hd, fn, unfold), quote(arg))
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)

  def quote(l: VFinLevel)(implicit k: Lvl): FinLevel =
    val fl = force(l)
    val vars = fl.vars.foldLeft(LZ + fl.k) { case (i, (x, n)) =>
      i max (LVar(mkLvl(x).toIx) + n)
    }
    fl.metas.foldLeft(vars) { case (i, (x, n)) =>
      i max (LMeta(lmetaId(x)) + n)
    }

  def quote(v: VLevel)(implicit l: Lvl): Level = v match
    case VOmega  => LOmega
    case VOmega1 => LOmega1
    case VFL(l)  => LFinLevel(quote(l))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VType(l)       => Type(quote(l))
      case VUnitType      => UnitType
      case VUnitValue     => UnitValue
      case VRigid(hd, sp) => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)  => quote(Meta(id), sp, unfold)

      case VLam(x, i, b) => Lam(x, i, quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, u1, b, u2) =>
        Pi(
          x,
          i,
          quote(t, unfold),
          quote(u1),
          quote(b(VVar(l)), unfold)(l + 1),
          quote(u2)
        )

      case VLamLvl(x, body) =>
        LamLvl(x, quote(body(VFinLevel.vr(l)), unfold)(l + 1))
      case VPiLvl(x, body, u) =>
        val v = VFinLevel.vr(l)
        PiLvl(x, quote(body(v), unfold)(l + 1), quote(u(v))(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, u1, b, u2) =>
        Sigma(
          x,
          quote(t, unfold),
          quote(u1),
          quote(b(VVar(l)), unfold)(l + 1),
          quote(u2)
        )

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = EEmpty): Tm =
    quote(eval(tm), UnfoldAll)
