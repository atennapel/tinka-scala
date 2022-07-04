import Common.*
import scala.collection.mutable.Map
import Core.Tm
import Value.Val
import Value.Val.VGlobal

object Globals:
  private val globals: Map[Name, GlobalEntry] = Map.empty

  final case class GlobalEntry(
      val name: Name,
      val ty: Tm,
      val vty: Val,
      val value: Tm,
      val vvalue: Val,
      val vglobal: Val
  )

  def addGlobal(g: GlobalEntry): Unit = globals.put(g.name, g)
  def getGlobal(x: Name): Option[GlobalEntry] = globals.get(x)
