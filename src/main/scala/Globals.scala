import Common.*
import Core.Tm
import Value.Val
import Value.Val.VGlobal
import scala.collection.immutable.ListMap

object Globals:
  private var globals: ListMap[Name, GlobalEntry] = ListMap.empty

  final case class GlobalEntry(
      val name: Name,
      val ty: Tm,
      val vty: Val,
      val value: Tm,
      val vvalue: Val,
      val vglobal: Val
  )

  def addGlobal(g: GlobalEntry): Unit = globals = globals + (g.name -> g)
  def getGlobal(x: Name): Option[GlobalEntry] = globals.get(x)

  def getGlobals(): List[(Name, GlobalEntry)] = globals.toList
