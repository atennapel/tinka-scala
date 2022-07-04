import Common.*
import scala.annotation.tailrec
import scala.collection.mutable.StringBuilder
import Errors.*

object Core:
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Tm, value: Tm, body: Tm)
    case Type

    case Pi(name: Name, ty: Tm, body: Tm)
    case Lam(name: Name, body: Tm)
    case App(fn: Tm, arg: Tm)

    override def toString: String = this match
      case Var(ix)                    => s"'$ix"
      case Global(name)               => name
      case Let(name, ty, value, body) => s"let $name : $ty = $value; $body"
      case Type                       => "Type"

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
