import Parser.parser
import Elaborator.elaborate
import Evaluation.nf
import Ctx.*
import Debug.*

import java.io.File
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  val tm = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
  debug(tm.toString)
  implicit val ctx: Ctx = Ctx.empty
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
