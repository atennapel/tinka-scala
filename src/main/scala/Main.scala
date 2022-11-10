import Common.*
import Presyntax.*
import Evaluation.*
import Elaboration.*
import PrimElaboration.elaboratePrims
import Debug.*
import Parser.parser
import Errors.*

import java.io.File
import scala.io.Source
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  implicit val ctx: Ctx = Ctx.empty()
  try
    val ptime = System.nanoTime
    elaboratePrims()
    val ptime1 = System.nanoTime - ptime
    println(s"prim elaboration time: ${ptime1 / 1000000}ms (${ptime1}ns)")
    val time = System.nanoTime
    val rtm = parser.parseFromFile((new File(filename))).flatMap(_.toTry).get
    val time1 = System.nanoTime - time
    debug(rtm)
    println(s"parsing time: ${time1 / 1000000}ms (${time1}ns)")
    val time2 = System.nanoTime
    val (etm, ety, elv) = elaborate(rtm)
    val time3 = System.nanoTime - time2
    println(s"elaboration time: ${time3 / 1000000}ms (${time3}ns)")
    println(
      s"total time: ${(ptime1 + time1 + time3) / 1000000}ms (${time1 + time3}ns)"
    )
    println("level:")
    println(ctx.pretty(elv))
    println("type:")
    println(ctx.pretty(ety))
    println("elaborated term:")
    println(ctx.pretty(etm))
    println("normal form:")
    println(ctx.pretty(nf(etm)))
  catch
    case err: ElabError =>
      println(err.getMessage)
      val (line, col) = err.pos
      if line > 0 && col > 0 then
        val lineSrc = Source.fromFile(filename, "utf8").getLines.toSeq(line - 1)
        println(lineSrc)
        println(s"${" " * (col - 1)}^")
      if isDebug then err.printStackTrace()
