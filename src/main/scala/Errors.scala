object Errors:
  sealed trait Error
  case class UnifyError(msg: String) extends Exception(msg) with Error

  sealed trait ElabError extends Error
  case class ElabUnifyError(msg: String) extends Exception(msg) with ElabError
  case class CannotInferError(msg: String) extends Exception(msg) with ElabError
  case class UndefVarError(msg: String) extends Exception(msg) with ElabError
  case class NotPiError(msg: String) extends Exception(msg) with ElabError
