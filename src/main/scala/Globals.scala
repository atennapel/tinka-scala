import Syntax.*
import Value.*
import scala.collection.mutable

object Globals:
  private val map: mutable.Map[String, GlobalEntry] = mutable.Map.empty

  def reset(): Unit = map.clear()

  case class GlobalEntry(uri: String, tm: Tm, ty: Ty, value: Val, vty: VTy)

  def addGlobal(uri: String, entry: GlobalEntry): Unit = map.put(uri, entry)
  def getGlobal(uri: String): Option[GlobalEntry] = map.get(uri)
