import Common.*
import Value.*
import Prims.*
import Evaluation.*
import Parser.parser
import Elaborator.elaborateTop
import Debug.*
import Errors.*

import scala.collection.mutable.Map

object PrimElaboration:
  def elaboratePrims(): Unit = PrimName.values.foreach { name =>
    debug(s"elaborate primitive $name")
    val tm = parser.parse(primTypeScript(name)).toTry.get
    val (etm, ety, elv) = elaborateTop(tm)
    ety.eval(Nil) match
      case VType(vlv) => addPrimType(name, etm.eval(Nil), vlv)
      case _          => throw Impossible
  }
