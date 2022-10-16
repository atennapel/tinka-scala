import Common.*
import Syntax.*

import scala.annotation.tailrec

object Pretty:
  private def prettySigma(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Sigma(DontBind, t, b) =>
      s"${prettyParen(t, true)} ** ${prettyPi(b)(DontBind.toName :: ns)}"
    case Sigma(DoBind(x0), t, b) =>
      val x = fresh(x0)
      s"($x : ${pretty(t)}) ** ${prettyPi(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, Expl, t, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), Expl, t, b) =>
      val x = fresh(x0)
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(x0, Impl, t, b) =>
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
      case rest => s". ${pretty(rest)(ns)}"
    s"\\${go(tm, ns, true)}"

  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String = tm match
    case Var(_)              => pretty(tm)
    case Type                => pretty(tm)
    case Pair(_, _)          => pretty(tm)
    case Proj(_, _)          => pretty(tm)
    case App(_, _, _) if app => pretty(tm)
    case _                   => s"(${pretty(tm)})"

  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(fn, arg, Expl) => s"${prettyApp(fn)} ${prettyParen(arg)}"
    case App(fn, arg, Impl) => s"${prettyApp(fn)} {${pretty(arg)}}"
    case fn                 => prettyParen(fn)

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd) => fst :: flattenPair(snd)
    case tm             => List(tm)

  @tailrec
  private def fresh(x: Name)(implicit ns: List[Name]): Name =
    if ns.contains(x) then fresh(Name(s"${x}'"))(ns) else x
  private def fresh(b: Bind)(implicit ns: List[Name]): Bind = b match
    case DoBind(x) => DoBind(fresh(x))
    case DontBind  => DontBind

  private def prettyLift(x: Bind, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x.toName :: ns)
  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix) => ix(ns).toString
    case Type    => "Type"

    case Let(x0, t, v, b) =>
      val x = fresh(x0)
      s"let $x : ${pretty(t)} = ${pretty(v)}; ${prettyLift(x, b)}"

    case App(_, _, _)   => prettyApp(tm)
    case Lam(_, _, _)   => prettyLam(tm)
    case Pi(_, _, _, _) => prettyPi(tm)
    case Sigma(_, _, _) => prettySigma(tm)

    case Proj(tm, proj) => s"${prettyParen(tm)}$proj"
    case Pair(_, _) =>
      val es = flattenPair(tm)
      s"(${es.map(pretty).mkString(", ")})"
