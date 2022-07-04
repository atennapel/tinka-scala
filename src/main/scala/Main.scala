import Parser.parseDecls
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
    val decls = parseDecls(contents) match
      case Parser.Success(x, _)         => x
      case err @ Parser.Failure(msg, _) => throw new Exception(err.toString)
      case err @ Parser.Error(msg, _)   => throw new Exception(err.toString)
    println(decls)
    elaborateDecls(decls)
  catch
    case exc: Exception =>
      println(exc.getMessage)
