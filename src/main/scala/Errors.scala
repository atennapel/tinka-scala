object Errors:
  final case class Impossible() extends Exception(s"impossible")
  final case class UnifyError() extends Exception(s"unify error")

  final case class ElaborationUnifyError(msg: String)
      extends Exception(s"unify error: $msg")
  final case class CannotInferError(msg: String)
      extends Exception(s"cannot infer: $msg")
  final case class NotPiError(msg: String) extends Exception(s"not a pi: $msg")
  final case class VarError(msg: String)
      extends Exception(s"undefined variable: $msg")
  final case class GlobalError(msg: String)
      extends Exception(s"duplicate global: $msg")
  final case class HoleError(msg: String) extends Exception(s"hole found: $msg")
