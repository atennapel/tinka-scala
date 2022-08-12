import Common.*
import Core.*
import Value.*
import Errors.*
import Surface as S

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val checks: ArrayBuffer[CheckEntry] = ArrayBuffer.empty

  enum CheckEntry:
    case Unchecked(ctx: Ctx, tm: S.Tm, ty: VTy, meta: MetaId)
    case Checked(tm: Tm)
  export CheckEntry.*

  def freshCheck(tm: S.Tm, ty: VTy, meta: MetaId)(implicit ctx: Ctx): CheckId =
    val id = checkId(checks.size)
    checks.addOne(Unchecked(ctx, tm, ty, meta))
    id

  def getCheck(id: CheckId): CheckEntry = checks(id.expose)

  def solveCheck(id: CheckId, tm: Tm): Unit =
    checks(id.expose) = Checked(tm)

  def nextCheckId(): Int = checks.size

  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  type Blocking = Set[CheckId]

  enum MetaEntry:
    case Unsolved(blocking: Blocking, ty: VTy)
    case Solved(value: Val, ty: VTy)
  export MetaEntry.*

  def freshMeta(blocking: Blocking, ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(blocking, ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)
  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_, _) => u
    case Solved(_, _)       => throw Impossible
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_, _)   => throw Impossible
    case s @ Solved(_, _) => s

  def addBlocking(id: MetaId, c: CheckId): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = u.copy(blocking = u.blocking + c)

  def solveMeta(id: MetaId, v: Val): Unit =
    val ty = getMetaUnsolved(id).ty
    metas(id.expose) = Solved(v, ty)

  def unsolvedMetas(): List[(MetaId, VTy)] = metas.zipWithIndex.collect {
    case (Unsolved(_, ty), ix) => (metaId(ix), ty)
  }.toList

  def reset(): Unit =
    checks.clear()
    metas.clear()
