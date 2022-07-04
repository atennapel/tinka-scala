import Common.*
import Common.BD.*
import Core.*
import Core.Tm.*
import Value.*
import Value.Head.*
import Value.Val.*
import Value.Elim.*
import Errors.*
import Globals.*
import Metas.*
import Metas.MetaEntry.*

object Evaluation:
  def vinst(cl: Clos, v: Val): Val = eval(v :: cl.env, cl.tm)

  def force(v: Val, forceGlobals: Boolean = true): Val = v match
    case VGlobal(_, _, value) if forceGlobals => force(value(), true)
    case ne @ VNe(HMeta(id), sp) =>
      getMeta(id) match
        case Unsolved    => ne
        case Solved(sol) => force(sp.foldRight(sol)(velim), forceGlobals)
    case _ => v

  def vapp(fn: Val, arg: Val): Val = fn match
    case VLam(_, body)  => vinst(body, arg)
    case VNe(hd, spine) => VNe(hd, EApp(arg) :: spine)
    case VGlobal(hd, spine, value) =>
      VGlobal(hd, EApp(arg) :: spine, () => vapp(value(), arg))
    case _ => throw Impossible()

  def velim(e: Elim, v: Val): Val = e match
    case EApp(arg) => vapp(v, arg)

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Unsolved  => VMeta(id)
    case Solved(v) => v

  def vinsertedmeta(env: Env, id: MetaId, bds: BDs): Val =
    def go(env: Env, bds: BDs): Val = (env, bds) match
      case (List(), List())           => vmeta(id)
      case (v :: env, Bound :: bds)   => vapp(go(env, bds), v)
      case (_ :: env, Defined :: bds) => go(env, bds)
      case _                          => throw Impossible()
    go(env, bds)

  def eval(env: Env, tm: Tm): Val = tm match
    case Var(ix) => ixEnv(env, ix)
    case Global(name) =>
      getGlobal(name) match
        case Some(ge) => ge.vglobal
        case None     => throw Impossible()
    case Let(x, _, value, body) => eval(eval(env, value) :: env, body)
    case Type                   => VType

    case Pi(x, ty, body) => VPi(x, eval(env, ty), Clos(env, body))
    case Lam(x, body)    => VLam(x, Clos(env, body))
    case App(fn, arg)    => vapp(eval(env, fn), eval(env, arg))

    case Meta(id)              => vmeta(id)
    case InsertedMeta(id, bds) => vinsertedmeta(env, id, bds)

  private def quoteSp(lvl: Lvl, tm: Tm, sp: Spine, forceGlobals: Boolean): Tm =
    sp match
      case List() => tm
      case EApp(arg) :: sp =>
        App(quoteSp(lvl, tm, sp, forceGlobals), quote(lvl, arg, forceGlobals))

  private def quoteHead(lvl: Lvl, head: Head): Tm = head match
    case HVar(head) => Var(lvl2ix(lvl, head))
    case HMeta(id)  => Meta(id)

  def quote(lvl: Lvl, value: Val, forceGlobals: Boolean = false): Tm =
    force(value, forceGlobals) match
      case VNe(head, sp) => quoteSp(lvl, quoteHead(lvl, head), sp, forceGlobals)
      case VGlobal(head, sp, _) => quoteSp(lvl, Global(head), sp, forceGlobals)
      case VType                => Type

      case VPi(x, ty, body) =>
        Pi(
          x,
          quote(lvl, ty, forceGlobals),
          quote(lvlInc(lvl), vinst(body, VVar(lvl)), forceGlobals)
        )
      case VLam(x, body) =>
        Lam(x, quote(lvlInc(lvl), vinst(body, VVar(lvl)), forceGlobals))

  def nf(env: Env, tm: Tm): Tm =
    quote(lvlFromEnv(env), eval(env, tm), forceGlobals = true)
