import Common.*
import Core.*
import Core.Tm.*
import Value.*
import Value.Val.*
import Value.Elim.*
import Errors.*

object Evaluation:
  def vinst(cl: Clos, v: => Val): Val = eval(v :: cl.env, cl.tm)

  def vapp(fn: Val, arg: => Val): Val = fn match
    case VLam(_, body)  => vinst(body, arg)
    case VNe(hd, spine) => VNe(hd, EApp(arg) :: spine)
    case _              => throw Impossible()

  def eval(env: Env, tm: Tm): Val = tm match
    case Var(ix)                => ixEnv(env, ix)
    case Let(x, _, value, body) => eval(eval(env, value) :: env, body)
    case Type                   => VType

    case Pi(x, ty, body) => vpi(x, eval(env, ty), Clos(env, body))
    case Lam(x, body)    => VLam(x, Clos(env, body))
    case App(fn, arg)    => vapp(eval(env, fn), eval(env, arg))

  private def quoteSp(lvl: Lvl, tm: Tm, sp: Spine): Tm = sp match
    case List()          => tm
    case EApp(arg) :: sp => App(quoteSp(lvl, tm, sp), quote(lvl, arg))

  def quote(lvl: Lvl, value: Val): Tm = value match
    case VNe(head, sp) => quoteSp(lvl, Var(lvl2ix(lvl, head)), sp)
    case VType         => Type

    case VPi(x, ty, body) =>
      Pi(x, quote(lvl, ty()), quote(lvlInc(lvl), vinst(body, VVar(lvl))))
    case VLam(x, body) => Lam(x, quote(lvlInc(lvl), vinst(body, VVar(lvl))))

  def nf(env: Env, tm: Tm): Tm = quote(lvlFromEnv(env), eval(env, tm))
