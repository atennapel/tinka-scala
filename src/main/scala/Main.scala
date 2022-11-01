import Parser.parser
import Debug.*

import java.io.File
import scala.io.Source
import parsley.io.given

@main def run(filename: String): Unit =
  setDebug(false)
  val tm = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
  println(tm)
