import Common.*
import Syntax.*

object Pretty:
  def pretty(l: Level)(implicit ns: List[Name]): String = l match
    case LOmega       => "omega"
    case LOmega1      => "omega1"
    case LFinLevel(l) => pretty(l)

  private def levelTryNat(l: FinLevel): Option[Int] = l match
    case LZ    => Some(0)
    case LS(l) => levelTryNat(l).map(_ + 1)
    case _     => None

  def pretty(l: FinLevel)(implicit ns: List[Name]): String =
    l match
      case LVar(ix) => ns(ix.expose).toString
      case LZ       => "0"
      case l @ LS(a) =>
        levelTryNat(l).map(_.toString).getOrElse(s"(S ${pretty(a)})")
      case LMax(a, b) =>
        s"(max ${pretty(a)} ${pretty(b)})" // TODO: handle parens better
      case LMeta(id)            => s"?l$id"
      case LInsertedMeta(id, _) => s"?*l$id"

  private def prettySigma(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Sigma(DontBind, t, _, b, _) =>
      s"${prettyParen(t, true)} ** ${prettyPi(b)(DontBind.toName :: ns)}"
    case Sigma(DoBind(x0), t, _, b, _) =>
      val x = fresh(x0)
      s"($x : ${pretty(t)}) ** ${prettyPi(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case PiLvl(x, b, _) => s"<$x> -> ${prettyPi(b)(x.toName :: ns)}"
    case Pi(DontBind, Expl, t, _, b, _) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), Expl, t, _, b, _) =>
      val x = fresh(x0)
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(x0, Impl, t, _, b, _) =>
      val x = fresh(x0)
      s"{$x : ${pretty(t)}} -> ${prettyPi(b)(x.toName :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, ns: List[Name], first: Boolean = false): String = tm match
      case Lam(x0, Expl, b) =>
        val x = fresh(x0)
        s"${if first then "" else " "}$x${go(b, x.toName :: ns)}"
      case Lam(x0, Impl, b) =>
        val x = fresh(x0)
        s"${if first then "" else " "}{$x}${go(b, x.toName :: ns)}"
      case LamLvl(x0, b) =>
        val x = fresh(x0)
        s"${if first then "" else " "}<$x>${go(b, x.toName :: ns)}"
      case rest => s". ${pretty(rest)(ns)}"
    s"\\${go(tm, ns, true)}"

  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String = tm match
    case Var(_)              => pretty(tm)
    case Global(_)           => pretty(tm)
    case Prim(_)             => pretty(tm)
    case Type(LFinLevel(LZ)) => pretty(tm)
    case Type(_) if app      => pretty(tm)
    case Pair(_, _)          => pretty(tm)
    case Proj(_, _)          => pretty(tm)
    case Meta(_)             => pretty(tm)
    case AppPruning(_, _)    => pretty(tm)
    case App(_, _, _) if app => pretty(tm)
    case Wk(tm)              => prettyParen(tm, app)(ns.tail)
    case _                   => s"(${pretty(tm)})"

  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(fn, arg, Expl) => s"${prettyApp(fn)} ${prettyParen(arg)}"
    case App(fn, arg, Impl) => s"${prettyApp(fn)} {${pretty(arg)}}"
    case AppLvl(fn, arg)    => s"${prettyApp(fn)} <${pretty(arg)}>"
    case fn                 => prettyParen(fn)

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd) => fst :: flattenPair(snd)
    case tm             => List(tm)

  private def prettyLift(x: Bind, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x.toName :: ns)
  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix)             => ns(ix.expose).toString
    case Prim(name)          => s"$name"
    case Global(x)           => s"#$x"
    case Type(LFinLevel(LZ)) => "Type"
    case Type(l)             => s"Type ${pretty(l)}"

    case Let(x0, t, v, b) =>
      val x = fresh(x0)
      s"let $x : ${pretty(t)} = ${pretty(v)}; ${prettyLift(x, b)}"

    case App(_, _, _)         => prettyApp(tm)
    case AppLvl(_, _)         => prettyApp(tm)
    case Lam(_, _, _)         => prettyLam(tm)
    case LamLvl(_, _)         => prettyLam(tm)
    case Pi(_, _, _, _, _, _) => prettyPi(tm)
    case PiLvl(_, _, _)       => prettyPi(tm)
    case Sigma(_, _, _, _, _) => prettySigma(tm)

    case Proj(tm, proj) => s"${prettyParen(tm)}$proj"
    case Pair(_, _) =>
      val es = flattenPair(tm)
      if es.last == Prim(PUnit) then s"[${es.init.map(pretty).mkString(", ")}]"
      else s"(${es.map(pretty).mkString(", ")})"

    case Wk(tm)            => pretty(tm)(ns.tail)
    case Meta(id)          => s"?$id"
    case AppPruning(fn, _) => s"?*${prettyParen(fn)}"
