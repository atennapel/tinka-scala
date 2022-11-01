import Presyntax.*
import Common.*

import parsley.Parsley, Parsley._
import scala.language.implicitConversions

object Parser:
  object LangLexer:
    import parsley.token.{LanguageDef, Lexer, Predicate, Parser}
    import parsley.character.{alphaNum, isWhitespace, char, oneOf}
    import parsley.combinator.{eof, many}

    private val userOps = "`~!@$%^&*-+=|:/?><,."
    private val userOpsTail = s"${userOps}#_;"
    private val uriCharsHead = "-_~:/?#@!$&'*+,%="
    private val uriChars = "-_~:/?#@!$&'*+,%="

    val lang = LanguageDef.plain.copy(
      commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      nestedComments = true,
      keywords =
        Set("Type", "let", "open", "hiding", "export", "if", "then", "else"),
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
    val uri: Parsley[String] =
      lexer.lexeme(
        char('#') *> (((alphaNum <|> oneOf(uriCharsHead*)) <~> many(
          alphaNum <|> oneOf(uriChars*)
        )).map { case (hd, tl) =>
          s"$hd${tl.mkString}"
        } <|> lexer.stringLiteral)
      )
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
    import parsley.Parsley.pos

    import LangLexer.{ident as ident0, userOp as userOp0, natural, uri}
    import LangLexer.Implicits.given

    private def positioned(p: => Parsley[RTm]): Parsley[RTm] =
      (pos <~> p).map(RPos.apply)
    private def positionedLevel(p: => Parsley[RLevel]): Parsley[RLevel] =
      (pos <~> p).map(RLPos.apply)

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val levelAtom: Parsley[RLevel] = positionedLevel(
      "(" *> level <* ")" <|> natural.map(n =>
        var c: RLevel = RLZ
        for (_ <- 0.until(n)) c = RLS(c)
        c
      ) <|> "_" #> RLHole <|> ident.map(RLVar.apply)
    )

    private lazy val level: Parsley[RLevel] = positionedLevel(
      ("S" *> levelAtom).map(RLS(_)) <|>
        ("max" *> levelAtom <~> levelAtom).map(RLMax(_, _)) <|>
        levelAtom
    )

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(DoBind.apply)

    private lazy val holeP: Parsley[RTm] =
      ("_" *> option(ident)).map(x => x.fold(hole)(x => RHole(Some(x))))

    private lazy val atom: Parsley[RTm] = positioned(
      ("(" *> (userOp
        .map(RVar.apply) <|> sepEndBy(tm, ",").map(mkPair)) <* ")") <|>
        (option("#").map(_.isDefined) <~> "[" *> sepEndBy(tm, ",") <* "]")
          .map(mkUnitPair) <|>
        holeP <|>
        attempt("Type" *> levelAtom).map(RType.apply) <|>
        "Type" #> RType(RLZ) <|> nat
        <|> ident.map(RVar.apply)
    )

    private val unittype = RVar(Name("()"))
    private val unit = RVar(Name("[]"))
    private val hole = RHole(None)

    private def mkPair(ts: List[RTm]): RTm = ts match
      case Nil => unittype
      case ts  => ts.reduceRight(RPair.apply)

    private val nil = RVar(Name("Nil"))
    private val cons = RVar(Name("::"))
    private def mkUnitPair(isList: Boolean, ts: List[RTm]): RTm =
      if isList then
        ts.foldRight(nil)((x, y) =>
          RApp(RApp(cons, x, RArgIcit(Expl)), y, RArgIcit(Expl))
        )
      else ts.foldRight(unit)(RPair.apply)

    private val nZ = RVar(Name("Z"))
    private val nS = RVar(Name("S"))
    private lazy val nat: Parsley[RTm] = natural.map(n =>
      var c: RTm = nZ
      for (_ <- 0.until(n)) c = RApp(nS, c, RArgIcit(Expl))
      c
    )

    lazy val tm: Parsley[RTm] = positioned(
      attempt(piOrSigma) <|> ifTm <|> let <|> lam <|>
        precedence[RTm](app)(
          Ops(InfixR)("**" #> ((l, r) => RSigma(DontBind, l, r))),
          Ops(InfixR)("->" #> ((l, r) => RPi(DontBind, Expl, l, r)))
        )
    )

    private lazy val piOrSigma: Parsley[RTm] =
      ((some(piSigmaParam) <|> app.map(t =>
        List(Right((List(DontBind), Expl, Some(t))))
      )) <~> ("->" #> false <|> "**" #> true) <~> tm)
        .map { case ((ps, isSigma), rt) =>
          ps.foldRight(rt) {
            case (Right((xs, i, ty)), rt) =>
              xs.foldRight(rt)((x, rt) =>
                if isSigma then RSigma(x, ty.getOrElse(hole), rt)
                else RPi(x, i, ty.getOrElse(hole), rt)
              )
            case (Left(xs), rt) =>
              xs.foldRight(rt)(RPiLvl(_, _))
          }
        }

    private type PiSigmaParam =
      Either[List[Bind], (List[Bind], Icit, Option[RTy])]

    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("<" *> some(bind) <* ">").map(Left.apply) <|>
        ("{" *> some(bind) <~> option(":" *> tm) <* "}").map((xs, ty) =>
          Right((xs, Impl, ty))
        ) <|>
        attempt("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
          Right((xs, Expl, Some(ty)))
        ) <|> ("(" <~> ")").map(_ =>
          Right((List(DontBind), Expl, Some(unittype)))
        )

    private val ifVar: RTm = RVar(Name("if_"))
    private val ifIndVar: RTm = RVar(Name("if-ind_"))
    private lazy val ifTm: Parsley[RTm] =
      ("if" *> tm <~> option(":" *> tm) <~> "then" *> tm <~> "else" *> tm)
        .map { case (((c, ty), t), f) =>
          RApp(
            RApp(
              RApp(
                ty.map(RApp(ifIndVar, _, RArgIcit(Expl))).getOrElse(ifVar),
                c,
                RArgIcit(Expl)
              ),
              t,
              RArgIcit(Expl)
            ),
            f,
            RArgIcit(Expl)
          )
        }

    private lazy val let: Parsley[RTm] =
      ("let" *> identOrOp <~> many(defParam) <~>
        option(":" *> tm) <~> "=" *> tm <~> ";" *> tm).map {
        case ((((x, ps), ty), v), b) =>
          RLet(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty),
            b
          )
      }

    private lazy val lam: Parsley[RTm] =
      ("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams(_, _))

    private type LamParam =
      Either[(List[Bind], Option[Name]), (List[Bind], RArgInfo, Option[RTy])]
    private lazy val lamParam: Parsley[LamParam] =
      attempt("<" *> some(bind) <~> "=" *> identOrOp <* ">").map((xs, i) =>
        Left((xs, Some(i)))
      ) <|>
        attempt(
          "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
        ).map { case ((xs, ty), y) => Right((xs, RArgNamed(y), ty)) } <|>
        attempt(piSigmaParam).map {
          case Right((xs, i, ty)) =>
            Right((xs, RArgIcit(i), ty))
          case Left(xs) => Left((xs, None))
        } <|>
        bind.map(x => Right((List(x), RArgIcit(Expl), None)))

    private type DefParam = Either[List[Bind], (List[Bind], Icit, Option[RTy])]
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => Right((List(x), Expl, None)))

    private lazy val app: Parsley[RTm] =
      precedence[RTm](appAtom)(
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

    private lazy val appAtom: Parsley[RTm] = positioned(
      (projAtom <~> many(arg) <~> option(let <|> lam)).map {
        case ((fn, args), opt) =>
          (args.flatten ++ opt.map(t => Right((t, RArgIcit(Expl)))))
            .foldLeft(fn) { case (fn, e) =>
              e.fold(
                (arg, i) => RAppLvl(fn, arg, i),
                (arg, i) => RApp(fn, arg, i)
              )
            }
      }
    )

    private type Arg = Either[(RLevel, Option[Name]), (RTm, RArgInfo)]

    private lazy val arg: Parsley[List[Arg]] =
      attempt("<" *> some(identOrOp) <~> "=" *> level <* ">").map((xs, l) =>
        xs.map(x => Left((l, Some(x))))
      ) <|> ("<" *> level <* ">").map(l => List(Left((l, None))))
        <|> attempt("{" *> some(identOrOp) <~> "=" *> tm <* "}").map((xs, t) =>
          xs.map(x => Right((t, RArgNamed(x))))
        ) <|> ("{" *> tm <* "}").map(t => List(Right((t, RArgIcit(Impl)))))
        <|> projAtom.map(t => List(Right((t, RArgIcit(Expl)))))

    private lazy val projAtom: Parsley[RTm] =
      positioned(
        (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(RProj.apply))
      )

    private lazy val proj: Parsley[RProjType] =
      ("." *> ("1" #> RFst <|> "2" #> RSnd <|> identOrOp.map(RNamed.apply)))

    private def typeFromParams(ps: List[DefParam], rt: RTy): RTy =
      ps.foldRight(rt)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(RPi(_, i, ty.getOrElse(hole), _))
          case Left(xs) =>
            xs.foldRight(b)(RPiLvl(_, _))
      )

    private def lamFromDefParams(
        ps: List[DefParam],
        b: RTm,
        useTypes: Boolean
    ): RTm =
      ps.foldRight(b)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(
              RLam(
                _,
                RArgIcit(i),
                if useTypes then Some(ty.getOrElse(hole)) else None,
                _
              )
            )
          case Left(xs) => xs.foldRight(b)(RLamLvl(_, None, _))
      )
    private def lamFromLamParams(ps: List[LamParam], b: RTm): RTm =
      ps.foldRight(b)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(
              RLam(_, i, ty, _)
            )
          case Left((xs, i)) => xs.foldRight(b)(RLamLvl(_, i, _))
      )

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))
    private def opL(o: String): Parsley[InfixL.Op[RTm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) =>
          RApp(RApp(RVar(Name(op)), l, RArgIcit(Expl)), r, RArgIcit(Expl))
      )
    private def opR(o: String): Parsley[InfixR.Op[RTm]] =
      attempt(userOpStart(o)).map(op =>
        (l, r) =>
          RApp(RApp(RVar(Name(op)), l, RArgIcit(Expl)), r, RArgIcit(Expl))
      )
    private def opP(o: String): Parsley[Prefix.Op[RTm]] =
      attempt(userOpStart(o)).map(op =>
        t => RApp(RVar(Name(op)), t, RArgIcit(Expl))
      )
    private def opLevel(s: String): List[Ops[RTm, RTm]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString))*),
        Ops(InfixL)(chars.map(c => opL(c.toString))*),
        Ops(InfixR)(chars.map(c => opR(c.toString))*)
      )
    private def ops(ss: String*): Seq[Ops[RTm, RTm]] =
      ss.map(opLevel).flatten

  lazy val parser: Parsley[RTm] = LangLexer.fully(TmParser.tm)
