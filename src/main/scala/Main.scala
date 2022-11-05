import Common.*
import Presyntax.*
import Evaluation.*
import Elaboration.*
import Debug.*
import Parser.parser
import Errors.*

import java.io.File
import scala.io.Source
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(true)
  implicit val ctx: Ctx = Ctx.empty()
  try
    val time = System.nanoTime
    val rtm = parser.parseFromFile((new File(filename))).flatMap(_.toTry).get
    val (etm, ety, elv) = elaborate(rtm)
    val time1 = System.nanoTime - time
    debug(rtm)
    println(s"time: ${time1 / 1000000}ms (${time1}ns)")
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
