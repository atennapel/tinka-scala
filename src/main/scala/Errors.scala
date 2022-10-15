import Common.*
import Ctx.*

object Errors:
  sealed trait Error
  case class UnifyError(msg: String) extends Exception(msg) with Error

  sealed trait ElabError extends Exception with Error:
    def ctx: Ctx
    def pos: Pos = ctx.pos
  case class ElabUnifyError(msg: String)(implicit val ctx: Ctx)
      extends Exception(msg)
      with ElabError
  case class CannotInferError(msg: String)(implicit val ctx: Ctx)
      extends Exception(msg)
      with ElabError
  case class UndefVarError(msg: String)(implicit val ctx: Ctx)
      extends Exception(msg)
      with ElabError
  case class NotPiError(msg: String)(implicit val ctx: Ctx)
      extends Exception(msg)
      with ElabError
