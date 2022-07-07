import Value.*
import Common.*
import Core.*
import Errors.*
import scala.collection.mutable.ArrayBuffer

object Metas:
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved
    case Solved(value: Val, tm: Tm)
  import MetaEntry.*

  def freshMeta(): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved)
    id

  def resetMetas(): Unit = metas.clear()
  def getMeta(id: MetaId): MetaEntry = metas(exposeMetaId(id))
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved         => throw Impossible()
    case s @ Solved(_, _) => s

  def solveMeta(id: MetaId, v: Val, tm: Tm): Unit =
    metas(exposeMetaId(id)) = Solved(v, tm)

  def unsolvedMetas(): List[MetaId] = metas.zipWithIndex.collect {
    case (Unsolved, ix) => metaId(ix)
  }.toList
