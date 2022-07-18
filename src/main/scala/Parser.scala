import Surface.*
import Surface.Tm.*
import Surface.Decl.*
import Surface.ProjType.*
import Common.*
import Common.Icit.*
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
    "{",
    "}",
    "#[",
    "[",
    "]",
    ":",
    "=",
    ";",
    "->",
    "**",
    ",",
    "._1",
    "._2"
  )
  lexical.reserved ++= Seq("Type", "let", "def", "import")

  type P[+A] = PackratParser[A]
  lazy val expr: P[Tm] = piOrSigma | funOrProd | application | notApp
  lazy val notApp: P[Tm] =
    unitType | unit | parens | listParens | unitParens | lambda | let | typeP | variable
  lazy val lambda: P[Tm] = positioned(
    ("\\" | "λ") ~> lamParam.+ ~ "." ~ expr ^^ { case ps ~ _ ~ b =>
      annotatedLamFromParams(ps, b)
    }
  )
  lazy val let: P[Tm] = positioned(
    "let" ~> ident ~ defParam.* ~ (":" ~> expr).? ~ "=" ~ expr ~ ";" ~ expr ^^ {
      case x ~ ps ~ ty ~ _ ~ v ~ _ ~ b =>
        if ps.isEmpty then Let(x, ty, v, b)
        else
          val pi = piFromParams(ps, ty.getOrElse(Hole(None)))
          val lams = unannotatedLamFromParams(ps, v)
          Let(x, Some(pi), lams, b)
    }
  )

  lazy val unitType: P[Tm] = positioned("(" ~ ")" ^^ { case _ => Var("()") })
  lazy val unit: P[Tm] = positioned("[" ~ "]" ^^ { case _ => Var("[]") })
  lazy val unitParens: P[Tm] = positioned(
    "[" ~> expr ~ ("," ~ expr).* <~ "]" ^^ { case fst ~ rest =>
      val all = fst :: rest.map(_._2)
      all.foldRight(Var("[]"))((t, acc) => Pair(t, acc))
    }
  )
  lazy val listParens: P[Tm] = positioned(
    "#[" ~> expr ~ ("," ~ expr).* <~ "]" ^^ { case fst ~ rest =>
      val all = fst :: rest.map(_._2)
      all.foldRight(Var("Nil"))((t, acc) =>
        App(App(Var("Cons"), t, Right(Expl)), acc, Right(Expl))
      )
    }
  )

  private type Arg = Either[ProjType, (Tm, Either[List[Name], Icit])]

  def applyArg(fn: Tm, arg: Arg): Tm = arg match
    case Left(p)                => Proj(fn, p)
    case Right((arg, Right(i))) => App(fn, arg, Right(i))
    case Right((arg, Left(xs))) =>
      xs.foldLeft(fn)((b, x) => App(b, arg, Left(x)))

  def prepareSpine(sp: List[Arg]): List[Arg] = sp match
    case Right((arg, Right(Expl))) :: Left(p) :: rest =>
      prepareSpine(Right((Proj(arg, p), Right(Expl))) :: rest)
    case arg :: rest => arg :: prepareSpine(rest)
    case Nil         => List.empty

  lazy val application: P[Tm] = positioned(expr ~ argument.+ ^^ {
    case fn ~ args => prepareSpine(args).foldLeft(fn)(applyArg)
  })
  lazy val argument: P[Arg] =
    ("{" ~> ident.+ ~ "=" ~ expr <~ "}" ^^ { case xs ~ _ ~ t =>
      Right((t, Left(xs)))
    })
      | ("{" ~> expr <~ "}" ^^ { case t => Right((t, Right(Impl))) })
      | ("._1" ^^ { case _ => Left(Fst) })
      | ("._2" ^^ { case _ => Left(Snd) })
      | ("." ~ ident ^^ { case _ ~ x => Left(Named(x)) })
      | notApp.map(t => Right((t, Right(Expl))))

  lazy val variable: P[Tm] = positioned(ident ^^ { x =>
    if x.startsWith("_") then
      Hole(if x.tail.isEmpty then None else Some(x.tail))
    else if x.startsWith("'") then LabelLit(x.tail)
    else Var(x)
  })
  lazy val parens: P[Tm] = positioned(
    "(" ~> expr ~ ("," ~ expr).* <~ ")" ^^ {
      case fst ~ Nil  => fst
      case fst ~ rest => Pair(fst, rest.map(_._2).reduceRight(Pair.apply))
    }
  )
  lazy val typeP: P[Tm] = positioned("Type" ^^ { _ => Type })
  lazy val piOrSigma: P[Tm] = positioned(
    piParam.+ ~ ("->" | "**") ~ expr ^^ { // TODO: make ** lower precedence
      case ps ~ "->" ~ rt =>
        ps.foldRight(rt) { case ((xs, ty, i), rt) =>
          xs.foldRight(rt) { case (x, rt) =>
            Pi(x, i, ty.getOrElse(Hole(None)), rt)
          }
        }
      case ps ~ "**" ~ rt =>
        ps.foldRight(rt) {
          case ((_, _, Impl), _) =>
            throw new Exception("sigma cannot have a implicit parameter")
          case ((xs, ty, _), rt) =>
            xs.foldRight(rt) { case (x, rt) =>
              Sigma(x, ty.getOrElse(Hole(None)), rt)
            }
        }
      case _ ~ x ~ _ => throw new Exception(s"invalid infix operator: $x")
    }
  )
  lazy val funOrProd: P[Tm] = positioned(
    expr ~ ("->" | "**") ~ expr ^^ {
      case fn ~ "->" ~ arg => Pi("_", Expl, fn, arg)
      case fn ~ "**" ~ arg => Sigma("_", fn, arg)
      case _ ~ x ~ _       => throw new Exception(s"invalid infix operator: $x")
    }
  )
  lazy val piParam: P[(List[Name], Option[Tm], Icit)] =
    ("{" ~> ident.+ ~ ":" ~ expr <~ "}" ^^ { case xs ~ _ ~ ty =>
      (xs, Some(ty), Impl)
    }) | ("{" ~> ident.+ <~ "}" ^^ { case xs =>
      (xs, None, Impl)
    }) | ("(" ~> ident.+ ~ ":" ~ expr <~ ")" ^^ { case xs ~ _ ~ ty =>
      (xs, Some(ty), Expl)
    })

  lazy val lamParam: P[(List[Name], Option[Tm], Either[Name, Icit])] =
    piParam.map { case (xs, ty, i) =>
      (xs, ty, Right(i))
    } | ("{" ~> ident ~ ":" ~ expr ~ "=" ~ ident <~ "}" ^^ {
      case x ~ _ ~ ty ~ _ ~ y => (List(x), Some(ty), Left(y))
    }) | ("{" ~> ident ~ "=" ~ ident <~ "}" ^^ { case x ~ _ ~ y =>
      (List(x), None, Left(y))
    }) | ident.map(x => (List(x), None, Right(Expl)))

  lazy val defParam: P[(List[Name], Option[Tm], Icit)] =
    piParam.map { case (xs, ty, i) =>
      (xs, ty, i)
    } | ident.map(x => (List(x), None, Expl))

  def parse(str: String): ParseResult[Tm] =
    val tokens = new lexical.Scanner(str)
    phrase(expr)(tokens)

  lazy val decls: P[Decls] = repsep((decl | importP), ";") <~ opt(";") ^^ {
    lst =>
      Decls(lst)
  }
  lazy val decl: P[Decl] = positioned(
    "def" ~> ident ~ defParam.* ~ opt(":" ~> expr) ~ "=" ~ expr ^^ {
      case id ~ ps ~ ty ~ _ ~ v =>
        if ps.isEmpty then
          ty.fold(Def(id, v))(ty => Def(id, Let(id, Some(ty), v, Var(id))))
        else
          val pi = piFromParams(ps, ty.getOrElse(Hole(None)))
          val lams = unannotatedLamFromParams(ps, v)
          Def(id, Let(id, Some(pi), lams, Var(id)))
    }
  )
  lazy val importP: P[Decl] = positioned(
    "import" ~> (ident | stringLit) ^^ { case id => Import(id) }
  )
  def piFromParams(
      ps: List[(List[Name], Option[Tm], Icit)],
      rt: Tm
  ): Tm =
    ps.foldRight(rt) { case ((xs, tyopt, i), rt) =>
      val pty = tyopt.getOrElse(Hole(None))
      xs.foldRight(rt)((x, rt) => Pi(x, i, pty, rt))
    }
  def unannotatedLamFromParams(
      ps: List[(List[Name], Option[Tm], Icit)],
      body: Tm
  ): Tm =
    ps.foldRight(body) { case ((xs, _, i), body) =>
      xs.foldRight(body)((x, body) => Lam(x, Right(i), None, body))
    }
  def annotatedLamFromParams(
      ps: List[(List[Name], Option[Tm], Either[Name, Icit])],
      body: Tm
  ): Tm =
    ps.foldRight(body) { case ((xs, ty, i), body) =>
      xs.foldRight(body)((x, body) => Lam(x, i, ty, body))
    }

  def parseDecls(str: String): ParseResult[Decls] =
    val tokens = new lexical.Scanner(str)
    phrase(decls)(tokens)

  private object Lexer extends StdLexical:
    final val EofCh: Char = '\u001a'

    override def letter =
      elem("letter", c => (c.isLetter && c != 'λ') || c == '\'')

    override def whitespace: Parser[Any] = rep[Any](
      whitespaceChar
        | '{' ~ '-' ~ commentEnd
        | '-' ~ '-' ~ rep(chrExcept(EofCh, '\n'))
        | '{' ~ '-' ~ rep(elem("", _ => true)) ~> err("unclosed comment")
    )

    private def commentEnd: Parser[Any] = (
      rep(chrExcept(EofCh, '-')) ~ '-' ~ '}' ^^ { _ => ' ' }
        | rep(chrExcept(EofCh, '-')) ~ '-' ~ commentEnd ^^ { _ => ' ' }
    )
