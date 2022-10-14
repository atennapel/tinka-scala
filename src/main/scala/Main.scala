import Common.*
import Presyntax.*
import Elaboration.*

@main def run(filename: String): Unit =
  val tm = RPi(DoBind("A"), RType, RPi(DontBind, RVar("A"), RVar("A")))
  println(tm)
  val (et, ty) = elaborate(tm)
  println(ty)
  println(et)
