import Common.*
import Presyntax.RTm.*
import Syntax.*
import Value.*
import Errors.*
import Presyntax.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val checks: ArrayBuffer[CheckEntry] = ArrayBuffer.empty
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  // postponed checks
  enum CheckEntry:
    case Unchecked(ctx: Ctx, tm: RTm, ty: VTy, meta: MetaId)
    case Checked(tm: Tm)
  export CheckEntry.*

  def freshCheck(ctx: Ctx, tm: RTm, ty: VTy, meta: MetaId): CheckId =
    val id = checkId(checks.size)
    checks.addOne(Unchecked(ctx, tm, ty, meta))
    id

  def nextCheckId(): Int = checks.size

  def modifyCheck(checkId: CheckId)(fn: CheckEntry => CheckEntry): Unit =
    checks(checkId.expose) = fn(checks(checkId.expose))

  def writeCheck(checkId: CheckId, entry: CheckEntry): Unit =
    modifyCheck(checkId)(_ => entry)

  def solveCheck(checkId: CheckId, tm: Tm): Unit =
    writeCheck(checkId, Checked(tm))

  def getCheck(checkId: CheckId): CheckEntry = checks(checkId.expose)

  def addBlocking(blocks: MetaId, blocked: CheckId): Unit =
    modifyMeta(blocks) {
      case Unsolved(bs, ty) => Unsolved(bs + blocked, ty)
      case _                => impossible()
    }

  // metas
  type Blocking = Set[CheckId]

  enum MetaEntry:
    case Unsolved(blocking: Blocking, ty: VTy)
    case Solved(value: Val, tm: Tm, ty: VTy)
  export MetaEntry.*

  def freshMeta(blocking: Blocking, ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(blocking, ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)
  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_, _) => u
    case Solved(_, _, _)    => impossible()
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_, _)      => impossible()
    case s @ Solved(_, _, _) => s
  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val, tm: Tm): Unit =
    val ty = getMetaUnsolved(id).ty
    metas(id.expose) = Solved(v, tm, ty)

  def unsolvedMetas(): List[(MetaId, VTy)] = metas.zipWithIndex.collect {
    case (Unsolved(_, ty), ix) => (metaId(ix), ty)
  }.toList

  def resetMetas(): Unit =
    checks.clear()
    metas.clear()
