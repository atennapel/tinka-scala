import Parser.parseDecls
import Elaboration.*
import Evaluation.*
import Ctx.*
import Globals.*
import Pretty.*
import Debug.*
import PrimitiveElaboration.*
import Surface.Decl.*
import scala.io.Source
import scala.util.parsing.input.OffsetPosition
import scala.collection.mutable.Buffer

@main def cliDebug(filename: String): Unit = run(filename, true)
@main def cli(filename: String): Unit = run(filename)

def run(filename: String, debug: Boolean = false): Unit =
  try
    setDebug(debug)

    elaboratePrimitives()

    runFile(filename)

    getGlobal("main") match
      case None =>
      case Some(ge) =>
        println(s"main : ${pretty(ge.ty)}")
        println(s"main = ${pretty(ge.value)}")
        println(s"${pretty(nf(List.empty, ge.value), hideImplicitApps = true)}")
  catch
    case exc: Exception =>
      println(exc.getMessage)

private val imported: Buffer[String] = Buffer()

private def runFile(filenameIn: String): Unit =
  val filename =
    if filenameIn.endsWith(".tinka") then filenameIn else s"$filenameIn.tinka"
  if !imported.contains(filename) then
    debug(s"run $filename")
    val src = Source.fromFile(filename)
    val contents = src.getLines.mkString("\n")
    val ctx = Ctx.empty(OffsetPosition(contents, 0))
    src.close()
    val decls = parseDecls(contents) match
      case Parser.Success(x, _)         => x
      case err @ Parser.Failure(msg, _) => throw new Exception(err.toString)
      case err @ Parser.Error(msg, _)   => throw new Exception(err.toString)
    decls.decls.foreach {
      case Import(name) =>
        runFile(name)
      case _ =>
    }
    debug(decls.toString)
    elaborateDecls(decls)
    imported.addOne(filename)
