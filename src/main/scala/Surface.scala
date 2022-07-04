import Common.*
import scala.util.parsing.input.Positional
import scala.annotation.tailrec
import scala.collection.mutable.StringBuilder
import Errors.*

object Surface:
  enum Decl extends Positional:
    case Def(name: Name, value: Tm)

    override def toString: String = this match
      case Def(x, v) => s"def $x = $v;"

  final case class Decls(val decls: List[Decl]):
    override def toString: String = decls.map(_.toString).mkString("\n")

  enum Tm extends Positional:
    case Var(name: Name)
    case Let(name: Name, ty: Option[Tm], value: Tm, body: Tm)
    case Type

    case Pi(name: Name, ty: Tm, body: Tm)
    case Lam(name: Name, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Hole

    override def toString: String = this match
      case Var(name) => name
      case Let(name, Some(ty), value, body) =>
        s"let $name : $ty = $value; $body"
      case Let(name, _, value, body) => s"let $name = $value; $body"
      case Type                      => "Type"
      case Hole                      => "_"

      case pi @ Pi(_, _, _) =>
        val (ps, rt) = pi.flattenPi()
        piToString(ps, rt)
      case lam @ Lam(_, _) =>
        val (ns, b) = lam.flattenLam()
        val nsStr = ns.mkString(" ")
        s"\\$nsStr. $b"
      case app @ App(_, _) =>
        val (fn, args) = app.flattenApp()
        val argsStr = args.map(_.toStringParens(false)).mkString(" ")
        s"${fn.toStringParens()} $argsStr"

    def toStringParens(appSimple: Boolean = true) =
      if isSimple(appSimple) then this.toString else s"($this)"

    private def piParamToString(ps: (Name, Tm)) = ps match
      case ("_", ty) => ty.toStringParens()
      case (x, ty)   => s"($x : $ty)"

    @tailrec
    private def piToString(
        ps: List[(Name, Tm)],
        rt: Tm,
        sb: StringBuilder = new StringBuilder,
        kind: Int = 0
    ): String = ps match
      case List() => sb.append(s" -> $rt").toString
      case p :: rest if kind == 0 =>
        piToString(
          rest,
          rt,
          sb.append(piParamToString(p)),
          if p._1 == "_" then 1 else 2
        )
      case (p @ ("_", ty)) :: rest =>
        piToString(
          rest,
          rt,
          sb.append(s" -> ${piParamToString(p)}"),
          if p._1 == "_" then 1 else 2
        )
      case (p @ (x, ty)) :: rest if kind == 1 =>
        piToString(
          rest,
          rt,
          sb.append(s" -> ${piParamToString(p)}"),
          if p._1 == "_" then 1 else 2
        )
      case (p @ (x, ty)) :: rest if kind == 2 =>
        piToString(
          rest,
          rt,
          sb.append(s" ${piParamToString(p)}"),
          if p._1 == "_" then 1 else 2
        )
      case _ => throw Impossible()

    def isSimple(appSimple: Boolean = true) = this match
      case Var(_)                 => true
      case Type                   => true
      case Hole                   => true
      case App(_, _) if appSimple => true
      case _                      => false

    def flattenPi(ns: List[(Name, Tm)] = List.empty): (List[(Name, Tm)], Tm) =
      this match
        case Pi(name, ty, body) => body.flattenPi(ns :+ (name, ty))
        case tm                 => (ns, tm)

    def flattenLam(ns: List[Name] = List.empty): (List[Name], Tm) = this match
      case Lam(name, body) => body.flattenLam(ns :+ name)
      case tm              => (ns, tm)

    def flattenApp(args: List[Tm] = List.empty): (Tm, List[Tm]) = this match
      case App(fn, arg) => fn.flattenApp(arg :: args)
      case tm           => (tm, args)
