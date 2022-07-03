import Parser.parse
import scala.io.Source
import Elaboration.*
import Evaluation.*
import Ctx.*
import scala.util.parsing.input.OffsetPosition

@main def cli(filename: String): Unit =
  try
    val src = Source.fromFile(filename)
    val contents = src.getLines.mkString
    val ctx = Ctx.empty(OffsetPosition(contents, 0))
    src.close()
    val tm = parse(contents).get
    println(tm)
    val (etm, ety) = elaborate(tm)
    println(ctx.pretty(etm))
    println(ctx.pretty(ety))
    println(ctx.pretty(nf(ctx.env, etm)))
  catch
    case exc: Exception =>
      println(exc.getMessage)
