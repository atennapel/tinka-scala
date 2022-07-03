import Common.*
import scala.collection.mutable.Map
import Core.Tm
import Value.Val

object Globals:
  private val globals: Map[Name, GlobalEntry] = Map.empty

  final case class GlobalEntry(
      name: Name,
      ty: Tm,
      vty: Val,
      value: Tm,
      vvalue: Val
  )

  def addGlobal(g: GlobalEntry): Unit = globals.put(g.name, g)
  def getGlobal(x: Name): Option[GlobalEntry] = globals.get(x)
