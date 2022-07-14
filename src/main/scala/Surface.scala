import Common.*
import Common.Icit.*
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

    case Pi(name: Name, icit: Icit, ty: Tm, body: Tm)
    case Lam(name: Name, icit: Either[Name, Icit], ty: Option[Tm], body: Tm)
    case App(fn: Tm, arg: Tm, icit: Either[Name, Icit])

    case Sigma(name: Name, ty: Tm, body: Tm)
    case Pair(fst: Tm, snd: Tm)

    case Hole

    override def toString: String = this match
      case Var(name) => name
      case Let(name, Some(ty), value, body) =>
        s"let $name : $ty = $value; $body"
      case Let(name, _, value, body) => s"let $name = $value; $body"
      case Type                      => "Type"
      case Hole                      => "_"

      case pi @ Pi(_, _, _, _) =>
        val (ps, rt) = pi.flattenPi()
        piToString(ps, rt)
      case lam @ Lam(_, _, _, _) =>
        val (ns, b) = lam.flattenLam()
        val nsStr = ns.map(lamParamToString).mkString(" ")
        s"\\$nsStr. $b"
      case app @ App(_, _, _) =>
        val (fn, args) = app.flattenApp()
        val argsStr = args.map(argToString).mkString(" ")
        s"${fn.toStringParens()} $argsStr"

      case sigma @ Sigma(_, _, _) =>
        val (ps, rt) = sigma.flattenSigma()
        sigmaToString(ps, rt)
      case pair @ Pair(_, _) =>
        val es = pair.flattenPair()
        s"(${es.mkString(", ")})"

    def toStringParens(
        appSimple: Boolean = true,
        sigmaSimple: Boolean = false
    ) =
      if isSimple(appSimple, sigmaSimple) then this.toString else s"($this)"

    private def argToString(arg: (Tm, Either[Name, Icit])) = arg match
      case (arg, Left(x))     => s"{$x = $arg}"
      case (arg, Right(Impl)) => s"{$arg}"
      case (arg, Right(Expl)) => arg.toStringParens(false)

    private def lamParamToString(p: (Name, Either[Name, Icit], Option[Tm])) =
      p match
        case (x, Left(y), tyopt) =>
          tyopt.fold(s"{$x = $y}")(ty => s"{$x : $ty = $y}")
        case (x, Right(Impl), tyopt) => tyopt.fold(s"{$x}")(ty => s"{$x : $ty}")
        case (x, Right(Expl), tyopt) => tyopt.fold(x)(ty => s"($x : $ty)")

    private def piParamToString(ps: (Name, Icit, Tm)) = ps match
      case ("_", Expl, ty) => ty.toStringParens()
      case (x, Impl, ty)   => s"{$x : $ty}"
      case (x, Expl, ty)   => s"($x : $ty)"

    @tailrec
    private def piToString(
        ps: List[(Name, Icit, Tm)],
        rt: Tm,
        sb: StringBuilder = new StringBuilder,
        kind: Int = 0
    ): String = ps match
      case Nil =>
        sb.append(s" -> ${rt.toStringParens(sigmaSimple = true)}").toString
      case p :: rest if kind == 0 =>
        piToString(
          rest,
          rt,
          sb.append(piParamToString(p)),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case (p @ ("_", Expl, ty)) :: rest =>
        piToString(
          rest,
          rt,
          sb.append(s" -> ${piParamToString(p)}"),
          1
        )
      case p :: rest if kind == 1 =>
        piToString(
          rest,
          rt,
          sb.append(s" -> ${piParamToString(p)}"),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case p :: rest if kind == 2 =>
        piToString(
          rest,
          rt,
          sb.append(s" ${piParamToString(p)}"),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case _ => throw Impossible()

    private def sigmaParamToString(ps: (Name, Tm)) = ps match
      case ("_", ty) => ty.toStringParens()
      case (x, ty)   => s"($x : $ty)"

    @tailrec
    private def sigmaToString(
        ps: List[(Name, Tm)],
        rt: Tm,
        sb: StringBuilder = new StringBuilder,
        kind: Int = 0
    ): String = ps match
      case Nil => sb.append(s" ** ${rt.toStringParens()}").toString
      case p :: rest if kind == 0 =>
        sigmaToString(
          rest,
          rt,
          sb.append(sigmaParamToString(p)),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case (p @ ("_", ty)) :: rest =>
        sigmaToString(
          rest,
          rt,
          sb.append(s" ** ${sigmaParamToString(p)}"),
          1
        )
      case p :: rest if kind == 1 =>
        sigmaToString(
          rest,
          rt,
          sb.append(s" ** ${sigmaParamToString(p)}"),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case p :: rest if kind == 2 =>
        sigmaToString(
          rest,
          rt,
          sb.append(s" ${sigmaParamToString(p)}"),
          if p._1 == "_" && p._2 == Expl then 1 else 2
        )
      case _ => throw Impossible()

    def isSimple(appSimple: Boolean = true, sigmaSimple: Boolean = false) =
      this match
        case Var(_)         => true
        case Type           => true
        case Hole           => true
        case App(_, _, _)   => appSimple
        case Sigma(_, _, _) => sigmaSimple
        case _              => false

    def flattenPi(
        ns: List[(Name, Icit, Tm)] = List.empty
    ): (List[(Name, Icit, Tm)], Tm) =
      this match
        case Pi(name, icit, ty, body) => body.flattenPi(ns :+ (name, icit, ty))
        case tm                       => (ns, tm)

    def flattenSigma(
        ns: List[(Name, Tm)] = List.empty
    ): (List[(Name, Tm)], Tm) =
      this match
        case Sigma(name, ty, body) => body.flattenSigma(ns :+ (name, ty))
        case tm                    => (ns, tm)

    def flattenLam(
        ns: List[(Name, Either[Name, Icit], Option[Tm])] = List.empty
    ): (List[(Name, Either[Name, Icit], Option[Tm])], Tm) = this match
      case Lam(name, icit, ty, body) => body.flattenLam(ns :+ (name, icit, ty))
      case tm                        => (ns, tm)

    def flattenApp(
        args: List[(Tm, Either[Name, Icit])] = List.empty
    ): (Tm, List[(Tm, Either[Name, Icit])]) = this match
      case App(fn, arg, icit) => fn.flattenApp((arg, icit) :: args)
      case tm                 => (tm, args)

    def flattenPair(): List[Tm] = this match
      case Pair(fst, snd) => fst :: snd.flattenPair()
      case tm             => List(tm)
