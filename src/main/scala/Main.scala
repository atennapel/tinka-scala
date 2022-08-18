import Parser.parser
import Elaborator.elaborate
import Evaluation.nf
import Ctx.*
import Debug.*
import Errors.*

import java.io.File
import scala.io.Source
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  val tm = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
  debug(tm.toString)
  implicit val ctx: Ctx = Ctx.empty
  try
    val time = System.nanoTime
    val (etm, ety) = elaborate(tm)
    val time1 = System.nanoTime - time
    println(s"time: ${time1 / 1000000}ms (${time1}ns)")
    println("type:")
    println(ety.prettyCtx)
    println("elaborated term:")
    println(etm.prettyCtx)
    println("normal form:")
    println(etm.nf.prettyCtx)
  catch
    case err: ElabError =>
      println(err.getMessage)
      val (line, col) = err.pos
      val lineSrc = Source.fromFile(filename, "utf8").getLines.toSeq(line - 1)
      println(lineSrc)
      println(s"${" " * (col - 1)}^")
