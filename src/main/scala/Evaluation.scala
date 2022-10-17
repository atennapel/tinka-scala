import Common.*
import Syntax.*
import Value.*
import Globals.getGlobal

object Evaluation:
  extension (c: Clos) def inst(v: Val): Val = eval(c.tm)(v :: c.env)

  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, b)  => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg, icit))
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
    case VUri(uri, sp, v) => VUri(uri, SProj(sp, proj), () => vproj(v(), proj))
    case _                => impossible()

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

  private def quote(hd: Tm, sp: Spine)(implicit l: Lvl): Tm = sp match
    case SId              => hd
    case SApp(fn, arg, i) => App(quote(hd, fn), quote(arg), i)
    case SProj(tm, proj)  => Proj(quote(hd, tm), proj)

  def quote(v: Val)(implicit l: Lvl): Tm = v match
    case VType          => Type
    case VRigid(hd, sp) => quote(Var(hd.toIx), sp)
    case VUri(_, _, v)  => quote(v()) // TODO: unfold modes/forcing

    case VLam(x, i, b)   => Lam(x, i, quote(b.inst(VVar(l)))(l + 1))
    case VPi(x, i, t, b) => Pi(x, i, quote(t), quote(b.inst(VVar(l)))(l + 1))

    case VPair(fst, snd) => Pair(quote(fst), quote(snd))
    case VSigma(x, t, b) => Sigma(x, quote(t), quote(b.inst(VVar(l)))(l + 1))

    case VUnitType  => UnitType
    case VUnitValue => UnitValue

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm = quote(eval(tm))
