import Parser.parseDecls
import scala.io.Source
import Elaboration.*
import Evaluation.*
import Ctx.*
import scala.util.parsing.input.OffsetPosition
import Globals.*
import Pretty.*

@main def cli(filename: String): Unit =
  try
    val src = Source.fromFile(filename)
    val contents = src.getLines.mkString("\n")
    val ctx = Ctx.empty(OffsetPosition(contents, 0))
    src.close()
    val decls = parseDecls(contents) match
      case Parser.Success(x, _)         => x
      case err @ Parser.Failure(msg, _) => throw new Exception(err.toString)
      case err @ Parser.Error(msg, _)   => throw new Exception(err.toString)
    println(decls)
    elaborateDecls(decls)

    getGlobal("main") match
      case None =>
      case Some(ge) =>
        println(s"main : ${pretty(ge.ty)}")
        println(s"main = ${pretty(ge.value)}")
        println(s"${pretty(nf(List.empty, ge.value))}")
  catch
    case exc: Exception =>
      println(exc.getMessage)
