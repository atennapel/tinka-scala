import Value.*
import Common.*

import scala.collection.mutable.ArrayBuffer

object Globals:
  private var globals: ArrayBuffer[GlobalEntry] = ArrayBuffer.empty

  final case class GlobalEntry(name: Name, ty: VTy, lv: VLevel, value: Val)

  def addGlobal(g: GlobalEntry): Unit =
    globals += g

  def getGlobal(x: Name): Option[(GlobalEntry, Lvl)] =
    globals.zipWithIndex
      .findLast((g, i) => g.name == x)
      .map((g, i) => (g, mkLvl(i)))

  def getGlobalByLvl(l: Lvl): Option[GlobalEntry] =
    if l.expose >= 0 && l.expose < globals.size then Some(globals(l.expose))
    else None
