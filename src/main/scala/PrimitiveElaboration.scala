import Common.*
import Primitives.*
import Elaboration.*
import Parser.parse
import Errors.*
import Core.Tm.Type

object PrimitiveElaboration:
  def elaboratePrimitives(): Unit = foreachPrimitive { (name, defn) =>
    val stm = parse(defn) match
      case Parser.Success(x, _) => x
      case err @ Parser.Failure(msg, _) =>
        throw PrimitiveFailedToParse(s"$name: $err")
      case err @ Parser.Error(msg, _) =>
        throw PrimitiveFailedToParse(s"$name: $err")
    val (ty, _) = elaborate(stm)
    (ty, Ctx.empty().eval(ty))
  }
