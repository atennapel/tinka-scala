import Common.*
import Presyntax.*
import Evaluation.*
import Elaboration.*
import PrimElaboration.elaboratePrims
import Debug.*
import Parser.parser
import Errors.*
import ModuleLoading.*
import Globals.getGlobal

import java.io.File
import scala.io.Source
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  implicit val ctx: Ctx = Ctx.empty((0, 0), Some(filename))
  try
    val ptime = System.nanoTime
    elaboratePrims()
    val ptime1 = System.nanoTime - ptime
    println(s"primitives time: ${ptime1 / 1000000}ms (${ptime1}ns)")
    val time = System.nanoTime
    val uri = load(filename)
    val time1 = System.nanoTime - time
    println(s"elaboration time: ${time1 / 1000000}ms (${time1}ns)")

    val entry = getGlobal(uri).get
    debug(entry.src)
    println(
      s"total time: ${(ptime1 + time1) / 1000000}ms (${ptime1 + time1}ns)"
    )
    println("level:")
    println(ctx.pretty(entry.lv))
    println("type:")
    println(ctx.pretty(entry.ty))
    println("elaborated term:")
    println(ctx.pretty(entry.tm))
    println("normal form:")
    println(ctx.pretty(nf(entry.tm)))
  catch
    case err: ElabError =>
      println(err.getMessage)
      val (line, col) = err.pos
      err.ctx.filename match
        case None => println(s"at line $line col $col (no filename)")
        case Some(filename) =>
          if line > 0 && col > 0 then
            val lineSrc =
              Source.fromFile(filename, "utf8").getLines.toSeq(line - 1)
            println(lineSrc)
            println(s"${" " * (col - 1)}^")
      if isDebug then err.printStackTrace()
