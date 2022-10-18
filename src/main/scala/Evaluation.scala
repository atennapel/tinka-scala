import Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.getGlobal

object Evaluation:
  extension (c: Clos) def inst(v: Val): Val = eval(c.tm)(v :: c.env)

  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, b)  => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg, icit))
    case VFlex(hd, sp)  => VFlex(hd, SApp(sp, arg, icit))
    case VUri(uri, sp, v) =>
      VUri(uri, SApp(sp, arg, icit), () => vapp(v(), arg, icit))
    case _ => impossible()

  def vproj(tm: Val, proj: ProjType): Val = tm match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp)   => VRigid(hd, SProj(sp, proj))
    case VFlex(hd, sp)    => VFlex(hd, SProj(sp, proj))
    case VUri(uri, sp, v) => VUri(uri, SProj(sp, proj), () => vproj(v(), proj))
    case _                => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId             => v
    case SApp(sp, a, i)  => vapp(vspine(v, sp), a, i)
    case SProj(sp, proj) => vproj(vspine(v, sp), proj)

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_)     => VMeta(id)

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (Nil, Nil)                => v
      case (t :: env, Some(i) :: pr) => vapp(vappPruning(v, pr)(env), t, i)
      case (_ :: env, None :: pr)    => vappPruning(v, pr)(env)
      case _                         => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Type    => VType
    case Var(ix) => env(ix)
    case Uri(uri) =>
      getGlobal(uri) match
        case None => impossible()
        case Some(e) =>
          val value = e.value
          VUri(uri, SId, () => value)
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)

    case Lam(x, i, b)   => VLam(x, i, Clos(b))
    case App(f, a, i)   => vapp(eval(f), eval(a), i)
    case Pi(x, i, t, b) => VPi(x, i, eval(t), Clos(b))

    case Pair(fst, snd) => VPair(eval(fst), eval(snd))
    case Proj(tm, proj) => vproj(eval(tm), proj)
    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))

    case UnitType  => VUnitType
    case UnitValue => VUnitValue

    case Wk(tm) => eval(tm)(env.tail)

    case Meta(id)           => vmeta(id)
    case AppPruning(tm, pr) => vappPruning(eval(tm), pr)

  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _, _) => force(vspine(v, sp))
        case Unsolved(_)     => v
    case VUri(_, _, w) if unfold == UnfoldAll => force(w(), UnfoldAll)
    case _                                    => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VType            => Type
      case VRigid(hd, sp)   => quote(Var(hd.toIx), sp, unfold)
      case VFlex(id, sp)    => quote(Meta(id), sp, unfold)
      case VUri(uri, sp, _) => quote(Uri(uri), sp, unfold)

      case VLam(x, i, b) => Lam(x, i, quote(b.inst(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b.inst(VVar(l)), unfold)(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b.inst(VVar(l)), unfold)(l + 1))

      case VUnitType  => UnitType
      case VUnitValue => UnitValue

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)
