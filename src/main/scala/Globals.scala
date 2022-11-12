import Syntax.*
import Value.*
import Presyntax.RTm
import scala.collection.mutable

object Globals:
  private val map: mutable.Map[String, GlobalEntry] = mutable.Map.empty

  def reset(): Unit = map.clear()

  case class GlobalEntry(
      uri: String,
      src: RTm,
      tm: Tm,
      ty: Ty,
      lv: Level,
      value: Val,
      vty: VTy,
      vl: VLevel
  )

  def addGlobal(uri: String, entry: GlobalEntry): Unit = map.put(uri, entry)
  def getGlobal(uri: String): Option[GlobalEntry] = map.get(uri)
