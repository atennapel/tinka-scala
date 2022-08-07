import Surface.*
import Common.*

import parsley.Parsley, Parsley._
import scala.language.implicitConversions

object Parser:
  object LangLexer:
    import parsley.token.{LanguageDef, Lexer, Predicate, Parser}
    import parsley.character.{alphaNum, isWhitespace}
    import parsley.combinator.eof

    private val userOps = "`~!@#$%^&*-+=|:/?><,."
    private val userOpsTail = userOps + "_;"

    val lang = LanguageDef.plain.copy(
      commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      nestedComments = true,
      keywords = Set("Type", "let", "if", "then", "else"),
      operators = Set("=", ":", ";", "\\", ".", "->", "_"),
      identStart = Predicate(_.isLetter),
      identLetter = Predicate(c => c.isLetterOrDigit || c == '_'),
      opStart = Predicate(userOps.contains(_)),
      opLetter = Predicate(userOpsTail.contains(_)),
      space = Predicate(isWhitespace)
    )
    val lexer = new Lexer(lang)

    def fully[A](p: => Parsley[A]): Parsley[A] = lexer.whiteSpace *> p <* eof

    val ident: Parsley[String] = lexer.identifier
    val userOp: Parsley[String] = lexer.userOp
    val natural: Parsley[Int] = lexer.natural
    def keyword(s: String): Parsley[Unit] = lexer.keyword(s)
    def symbol(s: String): Parsley[Unit] = void(lexer.symbol_(s))

    object Implicits:
      given Conversion[String, Parsley[Unit]] with
        def apply(s: String): Parsley[Unit] =
          if lang.keywords(s) then lexer.keyword(s)
          else if lang.operators(s) then lexer.maxOp(s)
          else void(lexer.symbol_(s))

  object TmParser:
    import parsley.expr.{precedence, Ops, InfixL, InfixR, Prefix, Postfix}
    import parsley.combinator.{many, some, option}

    import LangLexer.{ident as ident0, userOp as userOp0, natural}
    import LangLexer.Implicits.given

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(Bound.apply)

    private lazy val atom: Parsley[Tm] =
      ("(" *> (userOp.map(Var.apply) <|> tm <|> pure(UnitType)) <* ")") <|>
        ("[" *> pure(Unit) <* "]") <|>
        "_" #> Hole <|> "Type" #> Type <|> nat <|>
        ident.map(Var.apply)

    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))
    private lazy val nat: Parsley[Tm] = natural.map(n =>
      var c: Tm = nZ
      for (_ <- 0.until(n)) c = App(nS, c)
      c
    )

    lazy val tm: Parsley[Tm] = attempt(pi) <|> ifTm <|> let <|> lam <|>
      precedence[Tm](app)(Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, l, r))))

    private lazy val pi: Parsley[Tm] =
      (some(piParam) <~> "->" *> tm).map((ps, rt) =>
        ps.foldRight(rt) { case ((xs, ty), rt) =>
          xs.foldRight(rt)((x, rt) => Pi(x, ty.getOrElse(Hole), rt))
        }
      )

    private type PiParam = (List[Bind], Option[Ty])

    private lazy val piParam: Parsley[PiParam] =
      ("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) => (xs, Some(ty)))

    private val ifVar: Tm = Var(Name("if_"))
    private lazy val ifTm: Parsley[Tm] =
      ("if" *> tm <~> "then" *> tm <~> "else" *> tm).map { case ((c, t), f) =>
        App(App(App(ifVar, c), Lam(DontBind, None, t)), Lam(DontBind, None, f))
      }

    private lazy val let: Parsley[Tm] =
      ("let" *> identOrOp <~> many(param) <~>
        option(":" *> tm) <~> "=" *> tm <~> ";" *> tm).map {
        case ((((x, ps), ty), v), b) =>
          Let(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromParams(ps, v, ty.isEmpty),
            b
          )
      }

    private lazy val lam: Parsley[Tm] =
      ("\\" *> many(param) <~> "." *> tm).map(lamFromParams(_, _, true))

    private type Param = (List[Bind], Option[Ty])

    private lazy val param: Parsley[Param] =
      attempt("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
        (xs, Some(ty))
      )
        <|> bind.map(x => (List(x), None))

    private lazy val app: Parsley[Tm] =
      precedence[Tm](appAtom)(
        ops(
          "`@#?,.",
          "*/%",
          "+-",
          ":",
          "=!",
          "<>",
          "&",
          "^",
          "|",
          "$"
        )*
      )

    private lazy val appAtom: Parsley[Tm] =
      (atom <~> many(atom) <~> option(let <|> lam)).map {
        case ((fn, args), opt) =>
          (args ++ opt).foldLeft(fn)(App.apply)
      }

    private def typeFromParams(ps: List[Param], rt: Ty): Ty =
      ps.foldRight(rt)((x, b) =>
        x match
          case (xs, ty) => xs.foldRight(b)(Pi(_, ty.getOrElse(Hole), _))
      )

    private def lamFromParams(ps: List[Param], b: Tm, useTypes: Boolean): Tm =
      ps.foldRight(b)((x, b) =>
        x match
          case (xs, ty) =>
            xs.foldRight(b)(Lam(_, if useTypes then ty else None, _))
      )

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))
    private def opL(o: String): Parsley[InfixL.Op[Tm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) => App(App(Var(Name(op)), l), r)
      )
    private def opR(o: String): Parsley[InfixR.Op[Tm]] =
      attempt(userOpStart(o)).map(op => (l, r) => App(App(Var(Name(op)), l), r))
    private def opP(o: String): Parsley[Prefix.Op[Tm]] =
      attempt(userOpStart(o)).map(op => t => App(Var(Name(op)), t))
    private def opLevel(s: String): List[Ops[Tm, Tm]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString))*),
        Ops(InfixL)(chars.map(c => opL(c.toString))*),
        Ops(InfixR)(chars.map(c => opR(c.toString))*)
      )
    private def ops(ss: String*): Seq[Ops[Tm, Tm]] =
      ss.map(opLevel).flatten

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
