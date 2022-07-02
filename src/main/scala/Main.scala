import Parser.parse
import scala.io.Source
import Elaboration.*
import Evaluation.*

@main def cli(filename: String): Unit =
  val src = Source.fromFile(filename)
  val contents = src.getLines.mkString
  src.close()
  val tm = parse(contents).get
  println(tm)
  val (etm, ety) = elaborate(tm)
  println(etm)
  println(ety)
  println(nf(List.empty, etm))
