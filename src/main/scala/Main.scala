import Parser.{parse, parseDecls}
import Elaboration.*
import Evaluation.*
import Ctx.*
import Globals.*
import Pretty.*
import Debug.*
import PrimitiveElaboration.*
import Surface.Decl.*
import scala.io.Source
import scala.io.StdIn.readLine
import scala.util.parsing.input.OffsetPosition
import scala.collection.mutable.Buffer

@main def cliDebug(filename: String): Unit = run(filename, true)
@main def cli(filename: String): Unit = run(filename)

@main def repl(): Unit =
  println("tinka repl")
  var running = true
  elaboratePrimitives()
  while running do
    var mode = ""
    try
      print("> ")
      var inp = readLine()
      if inp == null || List(":q", ":quit").contains(inp) then running = false
      else
        if inp.startsWith(":t ") then
          mode = "t"
          inp = inp.drop(3)
        else if inp.startsWith(":e ") then
          mode = "e"
          inp = inp.drop(3)
        else if inp.startsWith(":f ") then
          mode = "f"
          inp = inp.drop(3)
        else if inp == ":defs" then
          mode = "s"
          getGlobals().foreach { case (x, e) =>
            println(s"$x : ${pretty(e.ty)}")
          }
        else if inp.startsWith(":import") || inp.startsWith(":def") then
          mode = "s"
          runDecls(inp.drop(1))
        else if inp.startsWith(":") then
          throw new Exception("invalid repl command")

        if mode != "s" then
          val tm = parse(inp) match
            case Parser.Success(x, _) => x
            case err @ Parser.Failure(msg, _) =>
              throw new Exception(err.toString)
            case err @ Parser.Error(msg, _) => throw new Exception(err.toString)

          val (etm, ety) = elaborate(tm, OffsetPosition(inp, 0))

          if mode == "t" then println(pretty(ety))
          else if mode == "e" then println(pretty(etm))
          else if mode == "f" then println(pretty(nf(List.empty, etm)))
          else println(pretty(nf(List.empty, etm), hideImplicitApps = true))
    catch case exc: Exception => println(exc.getMessage)

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
    src.close()
    runDecls(contents)
    imported.addOne(filename)

private def runDecls(contents: String): Unit =
  val decls = parseDecls(contents) match
    case Parser.Success(x, _)         => x
    case err @ Parser.Failure(msg, _) => throw new Exception(err.toString)
    case err @ Parser.Error(msg, _)   => throw new Exception(err.toString)
  decls.decls.foreach {
    case Import(name) =>
      runFile(name)
    case _ =>
  }
  elaborateDecls(decls, OffsetPosition(contents, 0))
