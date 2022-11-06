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
      extends Exception(s"cannot infer: $msg")
      with ElabError
  case class UndefVarError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"undefined variable: $msg")
      with ElabError
  case class UndefUriError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"unloaded uri: $msg")
      with ElabError
  case class NotPiError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"not a pi or icit mismatch: $msg")
      with ElabError
  case class NotSigmaError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"not a sigma: $msg")
      with ElabError
  case class HoleError(msg: String)(implicit val ctx: Ctx)
      extends Exception(msg)
      with ElabError
  case class NameNotInSigmaError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"name not found in sigma: $msg")
      with ElabError
  case class NamedImplicitError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"no implicit found with name: $msg")
      with ElabError
  case class IcitMismatchError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"icit mismatch: $msg")
      with ElabError
  case class UnsolvedMetasError(msg: String)(implicit val ctx: Ctx)
      extends Exception(s"unsolved metas: $msg")
      with ElabError
