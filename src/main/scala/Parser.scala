import Surface.*
import Surface.Tm.*
import Surface.Decl.*
import Surface.ProjType.*
import Common.*
import Common.Icit.*
import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.PackratParsers
import scala.annotation.tailrec

object Parser extends StdTokenParsers with PackratParsers:
  type Tokens = StdLexical
  val lexical = Lexer
  lexical.reserved ++= Seq("Type", "let", "def", "import")

  type P[+A] = PackratParser[A]
  lazy val expr: P[Tm] = piOrSigma | funOrProd | application | notApp
  lazy val notApp: P[Tm] =
    unitType | unit | ("(" ~> operator <~ ")" ^^ { case op =>
      Var(op)
    }) | parens | listParens | unitParens | lambda | let | typeP | nat | variable
  lazy val lambda: P[Tm] = positioned(
    ("\\" | "λ") ~> lamParam.+ ~ "." ~ expr ^^ { case ps ~ _ ~ b =>
      annotatedLamFromParams(ps, b)
    }
  )
  lazy val let: P[Tm] = positioned(
    "let" ~> parameterIdent ~ defParam.* ~ (":" ~> expr).? ~ "=" ~ expr ~ ";" ~ expr ^^ {
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

  enum Arg:
    case ArgProj(proj: ProjType)
    case ArgApp(tm: Tm, icit: Either[List[Name], Icit])
    case ArgOp(op: Name)
  import Arg.*

  def prec(op: Name) = op.head match
    case '*' => 99
    case '/' => 99
    case '%' => 99

    case '+' => 98
    case '-' => 98

    case ':' => 97

    case '=' => 96
    case '!' => 96

    case '<' => 95
    case '>' => 95

    case '&' => 94

    case '^' => 93

    case '|' => 92

    case '$' => 91
    case '_' => 91

    case _ => 999

  def rightAssoc(op: Name) = op.last == ':'

  def applyArg(fn: Tm, arg: Arg): Tm = arg match
    case ArgProj(p)            => Proj(fn, p)
    case ArgApp(arg, Right(i)) => App(fn, arg, Right(i))
    case ArgApp(arg, Left(xs)) =>
      xs.foldLeft(fn)((b, x) => App(b, arg, Left(x)))
    case ArgOp(op) => App(Var(op), fn, Right(Expl))

  def prepareSpine(sp: List[Arg]): List[Arg] = sp match
    case ArgApp(arg, Right(Expl)) :: ArgProj(p) :: rest =>
      prepareSpine(ArgApp(Proj(arg, p), Right(Expl)) :: rest)
    case arg :: rest => arg :: prepareSpine(rest)
    case Nil         => Nil

  def splitSpine(sp: List[Arg]): List[Either[Name, Tm]] =
    def appSpine(sp: List[Arg]): Tm = sp match
      case Nil           => throw new Exception("impossible")
      case ArgOp(_) :: _ => throw new Exception("impossible")
      case ArgProj(_) :: _ =>
        throw new Exception("projection in application head")
      case ArgApp(fn, Left(_)) :: _ =>
        throw new Exception("implicit in application head")
      case ArgApp(fn, Right(Impl)) :: _ =>
        throw new Exception("implicit in application head")
      case ArgApp(fn, Right(Expl)) :: sp => sp.foldLeft(fn)(applyArg)
    def split(
        sp: List[Arg],
        acc: List[Arg] = Nil
    ): List[Either[Name, Tm]] =
      (sp, acc) match
        case (Nil, Nil)             => Nil
        case (Nil, acc)             => List(Right(appSpine(acc.reverse)))
        case (ArgOp(op) :: sp, Nil) => Left(op) :: split(sp, Nil)
        case (ArgOp(op) :: sp, acc) =>
          List(Right(appSpine(acc.reverse))) ++ (Left(op) :: split(sp, Nil))
        case (arg :: sp, acc) => split(sp, arg :: acc)
    split(sp)

  def shunting(sp: List[Either[Name, Tm]]): Tm =
    @tailrec
    def stack(st: List[Tm], sp: List[Either[Name, Tm]]): Tm = (st, sp) match
      case (t :: _, Nil)         => t
      case (st, Right(t) :: ops) => stack(t :: st, ops)
      case (b :: a :: st, Left(x) :: ops) =>
        stack(App(App(Var(x), a, Right(Expl)), b, Right(Expl)) :: st, ops)
      case _ => throw new Exception("impossible")
    @tailrec
    def go(
        in: List[Either[Name, Tm]],
        out: List[Either[Name, Tm]],
        ops: List[Name]
    ): List[Either[Name, Tm]] = (in, out, ops) match
      case (Nil, out, Nil)            => out
      case (Nil, out, op :: ops)      => go(Nil, Left(op) :: out, ops)
      case (Right(t) :: st, out, ops) => go(st, Right(t) :: out, ops)
      case (Left(o1) :: st, out, o2 :: ops)
          if prec(o2) > prec(o1) || (prec(o1) == prec(o2) && !rightAssoc(
            o1
          )) =>
        go(Left(o1) :: st, Left(o2) :: out, ops)
      case (Left(o1) :: st, out, ops) => go(st, out, o1 :: ops)
    sp match
      case List(Left(op)) => Var(op)
      case List(Left(op), Right(t)) =>
        App(Var(op), t, Right(Expl))
      case List(Right(t), Left(op)) =>
        App(App(Var("flip"), Var(op), Right(Expl)), t, Right(Expl))
      case st => stack(Nil, go(st, Nil, Nil).reverse)

  lazy val application: P[Tm] = positioned(
    (operator.map(Left.apply) | expr.map(Right.apply)) ~ argument.+ ^^ {
      case fn ~ args =>
        val sp = prepareSpine(args)
        val spl =
          splitSpine(fn.fold(o => ArgOp(o), t => ArgApp(t, Right(Expl))) :: sp)
        shunting(spl)
    }
  )
  def operator: Parser[String] =
    elem("operator", _.isInstanceOf[Lexer.Operator]) ^^ (_.chars)
  lazy val argument: P[Arg] =
    ("{" ~> parameterIdent.+ ~ "=" ~ expr <~ "}" ^^ { case xs ~ _ ~ t =>
      ArgApp(t, Left(xs))
    })
      | ("{" ~> expr <~ "}" ^^ { case t => ArgApp(t, Right(Impl)) })
      | ("._1" ^^ { case _ => ArgProj(Fst) })
      | ("._2" ^^ { case _ => ArgProj(Snd) })
      | ("." ~ parameterIdent ^^ { case _ ~ x => ArgProj(Named(x)) })
      | (operator ^^ { case op => ArgOp(op) })
      | notApp.map(t => ArgApp(t, Right(Expl)))

  lazy val nat: P[Tm] = positioned(numericLit ^^ { n =>
    val m = n.toInt
    if m < 0 then throw new Exception("negative nat literal")
    else
      var c = Var("Z")
      for _ <- 1 to m do c = App(Var("S"), c, Right(Expl))
      c
  })
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
    ("{" ~> parameterIdent.+ ~ ":" ~ expr <~ "}" ^^ { case xs ~ _ ~ ty =>
      (xs, Some(ty), Impl)
    }) | ("{" ~> parameterIdent.+ <~ "}" ^^ { case xs =>
      (xs, None, Impl)
    }) | ("(" ~> parameterIdent.+ ~ ":" ~ expr <~ ")" ^^ { case xs ~ _ ~ ty =>
      (xs, Some(ty), Expl)
    })

  lazy val lamParam: P[(List[Name], Option[Tm], Either[Name, Icit])] =
    piParam.map { case (xs, ty, i) =>
      (xs, ty, Right(i))
    } | ("{" ~> parameterIdent ~ ":" ~ expr ~ "=" ~ parameterIdent <~ "}" ^^ {
      case x ~ _ ~ ty ~ _ ~ y => (List(x), Some(ty), Left(y))
    }) | ("{" ~> parameterIdent ~ "=" ~ parameterIdent <~ "}" ^^ {
      case x ~ _ ~ y =>
        (List(x), None, Left(y))
    }) | parameterIdent.map(x => (List(x), None, Right(Expl)))

  lazy val defParam: P[(List[Name], Option[Tm], Icit)] =
    piParam.map { case (xs, ty, i) =>
      (xs, ty, i)
    } | parameterIdent.map(x => (List(x), None, Expl))

  def parse(str: String): ParseResult[Tm] =
    val tokens = new lexical.Scanner(str)
    phrase(expr)(tokens)

  lazy val decls: P[Decls] = repsep((decl | importP), ";") <~ opt(";") ^^ {
    lst =>
      Decls(lst)
  }
  lazy val parameterIdent: P[Name] = ("(" ~> operator <~ ")") | ident
  lazy val decl: P[Decl] = positioned(
    "def" ~> parameterIdent ~ defParam.* ~ opt(":" ~> expr) ~ "=" ~ expr ^^ {
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

    delimiters ++= Seq(
      ".",
      "(",
      ")",
      "{",
      "}",
      "#[",
      "[",
      "]",
      ";",
      "._1",
      "._2"
    )
    val specialOps = Seq(
      "\\",
      "λ",
      ":",
      "=",
      "->",
      "**",
      ","
    )

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

    private lazy val _delim: Parser[Token] = {
      def parseDelim(s: String): Parser[Token] = accept(s.toList) ^^ { x =>
        Keyword(s)
      }

      val d = new Array[String](delimiters.size)
      delimiters.copyToArray(d, 0)
      scala.util.Sorting.quickSort(d)
      (d.toList map parseDelim).foldRight(
        failure("no matching delimiter"): Parser[Token]
      )((x, y) => y | x)
    }

    private val symbols = "~!@#$%^&*+=|\\-:?/><,:"
    private def symbol = elem("symbol", c => symbols.contains(c))

    case class Operator(op: String) extends Token:
      override def chars = op

    lazy val operator: Parser[Token] = rep(symbol) ^^ { opL =>
      val op = opL.mkString
      if specialOps.contains(op) then Keyword(op)
      else Operator(op)
    }

    override def delim: Parser[Token] = _delim | operator
