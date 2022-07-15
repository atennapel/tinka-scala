import Common.*
import Value.*
import Elaboration.*
import scala.collection.mutable.Map
import scala.collection.immutable.ListMap

object Primitives:
  private val primitives: Map[PrimName, Val] = Map.empty

  def foreachPrimitive(fn: (name: PrimName, defn: String) => Val): Unit =
    primitivesTypes.foreachEntry((name, defn) =>
      primitives.put(name, fn(name, defn))
    )

  def getPrimitive(name: PrimName): Option[Val] = primitives.get(name)

  private val primitivesTypes = ListMap(
    "()" -> "Type",
    "[]" -> "()"
  )
