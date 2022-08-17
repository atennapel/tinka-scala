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
      operators = Set("=", ":", ";", "\\", ".", ",", "#", "->", "**", "_"),
      identStart = Predicate(_.isLetter),
      identLetter =
        Predicate(c => c.isLetterOrDigit || c == '_' || c == '\'' || c == '-'),
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
    import parsley.combinator.{many, some, option, sepEndBy}

    import LangLexer.{ident as ident0, userOp as userOp0, natural}
    import LangLexer.Implicits.given

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(DoBind.apply)

    private lazy val atom: Parsley[Tm] =
      ("(" *> (userOp
        .map(Var.apply) <|> sepEndBy(tm, ",").map(mkPair)) <* ")") <|>
        (option("#").map(_.isDefined) <~> "[" *> sepEndBy(tm, ",") <* "]")
          .map(mkUnitPair) <|>
        "_" #> Hole <|> "Type" #> Type <|> nat <|>
        ident.map(Var.apply)

    private def mkPair(ts: List[Tm]): Tm = ts match
      case Nil => UnitType
      case ts  => ts.reduceRight(Pair.apply)

    private val nil = Var(Name("Nil"))
    private val cons = Var(Name("::"))
    private def mkUnitPair(isList: Boolean, ts: List[Tm]): Tm =
      if isList then
        ts.foldRight(nil)((x, y) =>
          App(App(cons, x, ArgIcit(Expl)), y, ArgIcit(Expl))
        )
      else ts.foldRight(Unit)(Pair.apply)

    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))
    private lazy val nat: Parsley[Tm] = natural.map(n =>
      var c: Tm = nZ
      for (_ <- 0.until(n)) c = App(nS, c, ArgIcit(Expl))
      c
    )

    lazy val tm: Parsley[Tm] = attempt(piOrSigma) <|> ifTm <|> let <|> lam <|>
      precedence[Tm](app)(
        Ops(InfixR)("**" #> ((l, r) => Sigma(DontBind, l, r))),
        Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, Expl, l, r)))
      )

    private lazy val piOrSigma: Parsley[Tm] =
      ((some(piSigmaParam) <|> app.map(t =>
        List((List(DontBind), Expl, Some(t)))
      )) <~> ("->" #> false <|> "**" #> true) <~> tm)
        .map { case ((ps, isSigma), rt) =>
          ps.foldRight(rt) { case ((xs, i, ty), rt) =>
            xs.foldRight(rt)((x, rt) =>
              if isSigma then Sigma(x, ty.getOrElse(Hole), rt)
              else Pi(x, i, ty.getOrElse(Hole), rt)
            )
          }
        }

    private type PiSigmaParam = (List[Bind], Icit, Option[Ty])

    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("{" *> some(bind) <~> option(":" *> tm) <* "}").map((xs, ty) =>
        (xs, Impl, ty)
      ) <|>
        attempt("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
          (xs, Expl, Some(ty))
        ) <|> ("(" <~> ")").map(_ => (List(DontBind), Expl, Some(UnitType)))

    private val ifVar: Tm = Var(Name("if_"))
    private val ifIndVar: Tm = Var(Name("if-ind_"))
    private lazy val ifTm: Parsley[Tm] =
      ("if" *> tm <~> option(":" *> tm) <~> "then" *> tm <~> "else" *> tm)
        .map { case (((c, ty), t), f) =>
          App(
            App(
              App(
                ty.map(App(ifIndVar, _, ArgIcit(Expl))).getOrElse(ifVar),
                c,
                ArgIcit(Expl)
              ),
              t,
              ArgIcit(Expl)
            ),
            f,
            ArgIcit(Expl)
          )
        }

    private lazy val let: Parsley[Tm] =
      ("let" *> identOrOp <~> many(defParam) <~>
        option(":" *> tm) <~> "=" *> tm <~> ";" *> tm).map {
        case ((((x, ps), ty), v), b) =>
          Let(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty),
            b
          )
      }

    private lazy val lam: Parsley[Tm] =
      ("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams(_, _))

    private type LamParam = (List[Bind], ArgInfo, Option[Ty])
    private lazy val lamParam: Parsley[LamParam] =
      attempt(
        "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
      ).map { case ((xs, ty), y) => (xs, ArgNamed(y), ty) } <|>
        attempt(piSigmaParam).map((xs, i, ty) => (xs, ArgIcit(i), ty)) <|>
        bind.map(x => (List(x), ArgIcit(Expl), None))

    private type DefParam = (List[Bind], Icit, Option[Ty])
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => (List(x), Expl, None))

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
          "$",
          "~"
        )*
      )

    private lazy val appAtom: Parsley[Tm] =
      (projAtom <~> many(arg) <~> option(let <|> lam)).map {
        case ((fn, args), opt) =>
          (args.flatten ++ opt.map((_, ArgIcit(Expl))))
            .foldLeft(fn) { case (fn, (arg, i)) => App(fn, arg, i) }
      }

    private type Arg = (Tm, ArgInfo)

    private lazy val arg: Parsley[List[Arg]] =
      attempt("{" *> some(identOrOp) <~> "=" *> tm <* "}").map((xs, t) =>
        xs.map(x => (t, ArgNamed(x)))
      ) <|> ("{" *> tm <* "}").map(t => List((t, ArgIcit(Impl))))
        <|> projAtom.map(t => List((t, ArgIcit(Expl))))

    private lazy val projAtom: Parsley[Tm] =
      (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(Proj.apply))

    private lazy val proj: Parsley[ProjType] =
      ("." *> ("1" #> Fst <|> "2" #> Snd <|> identOrOp.map(Named.apply)))

    private def typeFromParams(ps: List[DefParam], rt: Ty): Ty =
      ps.foldRight(rt)((x, b) =>
        x match
          case (xs, i, ty) =>
            xs.foldRight(b)(Pi(_, i, ty.getOrElse(Hole), _))
      )

    private def lamFromDefParams(
        ps: List[DefParam],
        b: Tm,
        useTypes: Boolean
    ): Tm =
      ps.foldRight(b)((x, b) =>
        x match
          case (xs, i, ty) =>
            xs.foldRight(b)(
              Lam(
                _,
                ArgIcit(i),
                if useTypes then Some(ty.getOrElse(Hole)) else None,
                _
              )
            )
      )
    private def lamFromLamParams(ps: List[LamParam], b: Tm): Tm =
      ps.foldRight(b)((x, b) =>
        x match
          case (xs, i, ty) =>
            xs.foldRight(b)(
              Lam(_, i, ty, _)
            )
      )

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))
    private def opL(o: String): Parsley[InfixL.Op[Tm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) => App(App(Var(Name(op)), l, ArgIcit(Expl)), r, ArgIcit(Expl))
      )
    private def opR(o: String): Parsley[InfixR.Op[Tm]] =
      attempt(userOpStart(o)).map(op =>
        (l, r) => App(App(Var(Name(op)), l, ArgIcit(Expl)), r, ArgIcit(Expl))
      )
    private def opP(o: String): Parsley[Prefix.Op[Tm]] =
      attempt(userOpStart(o)).map(op =>
        t => App(Var(Name(op)), t, ArgIcit(Expl))
      )
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
