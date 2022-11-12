import Common.*
import Value.*
import Prims.*
import Evaluation.*
import Parser.parser
import Elaboration.elaborate
import Ctx.*
import Debug.*
import Errors.*

import scala.collection.mutable.Map

object PrimElaboration:
  def elaboratePrims(): Unit = PrimName.values.foreach { name =>
    debug(s"elaborate primitive $name")
    val tm = parser.parse(primTypeScript(name)).toTry.get
    val (etm, ety, elv) = elaborate(tm)(Ctx.empty((0, 0), None))
    eval(ety)(EEmpty) match
      case VType(vlv) => addPrimType(name, eval(etm)(EEmpty), vlv)
      case _          => impossible()
  }
