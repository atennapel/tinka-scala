import Parser.parse
import scala.io.Source

@main def cli(filename: String): Unit =
  val src = Source.fromFile(filename)
  val contents = src.getLines.mkString
  src.close()
  val tm = parse(contents)
  println(tm)
