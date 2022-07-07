import Surface.*
import Surface.Tm.*
import Surface.Decl.*
import Common.*
import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.PackratParsers

object Parser extends StdTokenParsers with PackratParsers:
  type Tokens = StdLexical
  val lexical = Lexer
  lexical.delimiters ++= Seq(
    "\\",
    "λ",
    ".",
    "(",
    ")",
    ":",
    "=",
    ";",
    "->"
  )
  lexical.reserved ++= Seq("Type", "let", "def")

  type P[+A] = PackratParser[A]
  lazy val expr: P[Tm] = pi | fun | application | notApp
  lazy val notApp: P[Tm] =
    parens | lambda | let | typeP | variable
  lazy val lambda: P[Tm] = positioned(("\\" | "λ") ~> ident.+ ~ "." ~ expr ^^ {
    case xs ~ _ ~ b => xs.foldRight(b)(Lam.apply)
  })
  lazy val let: P[Tm] = positioned(
    "let" ~> ident ~ lamParam.* ~ (":" ~> expr).? ~ "=" ~ expr ~ ";" ~ expr ^^ {
      case x ~ ps ~ ty ~ _ ~ v ~ _ ~ b =>
        if ps.isEmpty then Let(x, ty, v, b)
        else
          val pi = piFromParams(ps, ty.getOrElse(Hole))
          val lams = unannotatedLamFromParams(ps, v)
          Let(x, Some(pi), lams, b)
    }
  )
  lazy val application: P[Tm] = positioned(expr ~ notApp ^^ { case fn ~ arg =>
    App(fn, arg)
  })
  lazy val variable: P[Tm] = positioned(ident ^^ { x =>
    if x.startsWith("_") then Hole else Var(x)
  })
  lazy val parens: P[Tm] = "(" ~> expr <~ ")"
  lazy val typeP: P[Tm] = positioned("Type" ^^ { _ => Type })
  lazy val pi: P[Tm] = positioned(
    piParam.+ ~ "->" ~ expr ^^ { case ps ~ _ ~ rt =>
      ps.foldRight(rt) { case ((xs, ty), rt) =>
        xs.foldRight(rt) { case (x, rt) => Pi(x, ty, rt) }
      }
    }
  )
  lazy val fun: P[Tm] = positioned(
    expr ~ "->" ~ expr ^^ { case fn ~ _ ~ arg => Pi("_", fn, arg) }
  )
  lazy val piParam: P[(List[Name], Tm)] =
    "(" ~> ident.+ ~ ":" ~ expr <~ ")" ^^ { case xs ~ _ ~ ty =>
      (xs, ty)
    }

  lazy val lamParam: P[(List[Name], Option[Tm])] = piParam.map {
    case (xs, ty) => (xs, Some(ty))
  } | ident.map(x => (List(x), None))

  def parse(str: String): ParseResult[Tm] =
    val tokens = new lexical.Scanner(str)
    phrase(expr)(tokens)

  lazy val decls: P[Decls] = repsep(decl, ";") <~ opt(";") ^^ { lst =>
    Decls(lst)
  }
  lazy val decl: P[Decl] = positioned(
    "def" ~> ident ~ lamParam.* ~ opt(":" ~> expr) ~ "=" ~ expr ^^ {
      case id ~ ps ~ ty ~ _ ~ v =>
        if ps.isEmpty then
          ty.fold(Def(id, v))(ty => Def(id, Let(id, Some(ty), v, Var(id))))
        else
          val pi = piFromParams(ps, ty.getOrElse(Hole))
          val lams = unannotatedLamFromParams(ps, v)
          Def(id, Let(id, Some(pi), lams, Var(id)))
    }
  )
  def piFromParams(ps: List[(List[Name], Option[Tm])], rt: Tm): Tm =
    ps.foldRight(rt) { case ((xs, tyopt), rt) =>
      val pty = tyopt.getOrElse(
        Hole
      ) // TODO: should the params share the same hole? (introduce let)
      xs.foldRight(rt)((x, rt) => Pi(x, pty, rt))
    }
  def unannotatedLamFromParams(
      ps: List[(List[Name], Option[Tm])],
      body: Tm
  ): Tm =
    ps.foldRight(body) { case ((xs, _), body) =>
      xs.foldRight(body)((x, body) => Lam(x, body))
    }

  def parseDecls(str: String): ParseResult[Decls] =
    val tokens = new lexical.Scanner(str)
    phrase(decls)(tokens)

  private object Lexer extends StdLexical:
    override def letter = elem("letter", c => c.isLetter && c != 'λ')
