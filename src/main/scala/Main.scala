import Parser.parseDecls
import Elaboration.*
import Evaluation.*
import Ctx.*
import Globals.*
import Pretty.*
import Debug.setDebug
import scala.io.Source
import scala.util.parsing.input.OffsetPosition

@main def cliDebug(filename: String): Unit = run(filename, true)
@main def cli(filename: String): Unit = run(filename)

def run(filename: String, debug: Boolean = false): Unit =
  try
    setDebug(debug)
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
