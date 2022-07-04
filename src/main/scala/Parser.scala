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
    "let" ~> ident ~ (":" ~> expr).? ~ "=" ~ expr ~ ";" ~ expr ^^ {
      case x ~ ty ~ _ ~ v ~ _ ~ b => Let(x, ty, v, b)
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

  def parse(str: String): ParseResult[Tm] =
    val tokens = new lexical.Scanner(str)
    phrase(expr)(tokens)

  lazy val decls: P[Decls] = repsep(decl, ";") <~ opt(";") ^^ { lst =>
    Decls(lst)
  }
  lazy val decl: P[Decl] = positioned(
    "def" ~> ident ~ opt(":" ~> expr) ~ "=" ~ expr ^^ { case id ~ ty ~ _ ~ v =>
      ty.fold(Def(id, v))(ty => Def(id, Let(id, Some(ty), v, Var(id))))
    }
  )

  def parseDecls(str: String): ParseResult[Decls] =
    val tokens = new lexical.Scanner(str)
    phrase(decls)(tokens)

  private object Lexer extends StdLexical:
    override def letter = elem("letter", c => c.isLetter && c != 'λ')
