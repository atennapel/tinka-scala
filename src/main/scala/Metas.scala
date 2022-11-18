import Common.*
import Presyntax.RTm.*
import Syntax.*
import Value.*
import Presyntax.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private var metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private var lmetas: ArrayBuffer[LMetaEntry] = ArrayBuffer.empty
  private type Frame = (ArrayBuffer[MetaEntry], ArrayBuffer[LMetaEntry])
  private var frames: ArrayBuffer[Frame] = ArrayBuffer.empty

  // metas
  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val, tm: Tm, ty: VTy)
  export MetaEntry.*

  def freshMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)
  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_) => u
    case Solved(_, _, _) => impossible()
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_)         => impossible()
    case s @ Solved(_, _, _) => s
  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val, tm: Tm): Unit =
    val ty = getMetaUnsolved(id).ty
    metas(id.expose) = Solved(v, tm, ty)

  def unsolvedMetas(): List[(MetaId, VTy)] = metas.zipWithIndex.collect {
    case (Unsolved(ty), ix) => (metaId(ix), ty)
  }.toList

  // universe level metas
  enum LMetaEntry:
    case LUnsolved
    case LSolved(dom: Lvl, value: VFinLevel)
  export LMetaEntry.*

  def freshLMeta(): LMetaId =
    val id = lmetaId(lmetas.size)
    lmetas.addOne(LUnsolved)
    id

  def getLMeta(id: LMetaId): LMetaEntry = lmetas(id.expose)
  def getLMetaSolved(id: LMetaId): LSolved = getLMeta(id) match
    case LUnsolved         => impossible()
    case s @ LSolved(_, _) => s
  def modifyLMeta(id: LMetaId)(fn: LMetaEntry => LMetaEntry): Unit =
    lmetas(id.expose) = fn(lmetas(id.expose))

  def solveLMeta(id: LMetaId, dom: Lvl, v: VFinLevel): Unit =
    lmetas(id.expose) = LSolved(dom, v)

  def unsolvedLMetas(): List[LMetaId] = lmetas.zipWithIndex.collect {
    case (LUnsolved, ix) => lmetaId(ix)
  }.toList

  def resetMetas(): Unit =
    lmetas.clear()
    metas.clear()
    frames.clear()

  def storeMetas(): Unit =
    frames += ((metas.clone(), lmetas.clone()))

  def restoreMetas(): Unit =
    val last = frames.remove(frames.size - 1)
    metas = last._1
    lmetas = last._2

  def skipMetas(): Unit =
    frames.remove(frames.size - 1)
    ()
