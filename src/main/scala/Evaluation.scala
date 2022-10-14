import Common.*
import Syntax.*
import Value.*

object Evaluation:
  extension (c: Clos) def inst(v: Val): Val = eval(c.tm)(v :: c.env)

  def vapp(fn: Val, arg: Val): Val = fn match
    case VLam(_, b)     => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg))
    case _              => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Type            => VType
    case Var(ix)         => env(ix)
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)

    case Lam(x, b)   => VLam(x, Clos(b))
    case App(f, a)   => vapp(eval(f), eval(a))
    case Pi(x, t, b) => VPi(x, eval(t), Clos(b))

  private def quote(hd: Tm, sp: Spine)(implicit l: Lvl): Tm = sp match
    case SId           => hd
    case SApp(fn, arg) => App(quote(hd, fn), quote(arg))

  def quote(v: Val)(implicit l: Lvl): Tm = v match
    case VType          => Type
    case VRigid(hd, sp) => quote(Var(hd.toIx), sp)

    case VLam(x, b)   => Lam(x, quote(b.inst(VVar(l)))(l + 1))
    case VPi(x, t, b) => Pi(x, quote(t), quote(b.inst(VVar(l)))(l + 1))
