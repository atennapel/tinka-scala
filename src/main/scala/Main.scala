import Parser.parser
import Elaboration.elaborate
import Evaluation.nf
import Debug.*

import java.io.File
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  val tm = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
  println("input:")
  println(tm.toString)
  val time = System.nanoTime
  val (etm, ety) = elaborate(tm)
  println(s"time: ${System.nanoTime - time}ns")
  println("type:")
  println(ety.toString)
  println("elaborated term:")
  println(etm.toString)
  println("normal form:")
  println(etm.nf.toString)
