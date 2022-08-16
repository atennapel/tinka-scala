import Common.*
import Core.*
import Value.*
import Errors.*
import Surface as S

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val checks: ArrayBuffer[PostponeEntry] = ArrayBuffer.empty

  enum CheckEntry:
    case Unchecked(ctx: Ctx, tm: S.Tm, ty: VTy, meta: MetaId)
    case Checked(tm: Tm)
  export CheckEntry.*

  enum UnifyEntry:
    case UnifyPostpone(k: Lvl, v1: Val, v2: Val)
    case UnifyDone
  export UnifyEntry.*

  enum PostponeEntry:
    case PostponeCheck(entry: CheckEntry)
    case PostponeUnify(entry: UnifyEntry)
  export PostponeEntry.*

  def freshCheck(tm: S.Tm, ty: VTy, meta: MetaId)(implicit
      ctx: Ctx
  ): PostponeId =
    val id = postponeId(checks.size)
    checks.addOne(PostponeCheck(Unchecked(ctx, tm, ty, meta)))
    id

  def freshPostponedUnif(
      k: Lvl,
      v1: Val,
      v2: Val
  ): PostponeId =
    val cid = postponeId(checks.size)
    checks.addOne(PostponeUnify(UnifyPostpone(k, v1, v2)))
    cid

  def getPostpone(id: PostponeId): PostponeEntry = checks(id.expose)

  def getCheck(id: PostponeId): CheckEntry = checks(id.expose) match
    case PostponeCheck(entry) => entry
    case _                    => throw Impossible

  def solveCheck(id: PostponeId, tm: Tm): Unit =
    checks(id.expose) = PostponeCheck(Checked(tm))

  def solvePostponeUnify(id: PostponeId): Unit =
    checks(id.expose) = PostponeUnify(UnifyDone)

  def nextCheckId(): Int = checks.size

  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  type Blocking = Set[PostponeId]

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

  def addBlocking(id: MetaId, c: PostponeId): Unit =
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
