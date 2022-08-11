import Common.*
import Core.*
import Value.*
import Errors.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved
    case Solved(value: Val)
  export MetaEntry.*

  def freshMeta(): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved)
    id

  def resetMetas(): Unit = metas.clear()
  def getMeta(id: MetaId): MetaEntry = metas(id.expose)
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved      => throw Impossible
    case s @ Solved(_) => s

  def solveMeta(id: MetaId, v: Val): Unit =
    metas(id.expose) = Solved(v)

  def unsolvedMetas(): List[MetaId] = metas.zipWithIndex.collect {
    case (Unsolved, ix) => metaId(ix)
  }.toList
