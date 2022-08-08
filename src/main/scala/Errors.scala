object Errors:
  object Impossible extends Exception("impossible")

  final case class UnifyError(msg: String)
      extends Exception(s"unify error: $msg")

  final case class ElabUnifyError(msg: String)
      extends Exception(s"unify error: $msg")
  final case class CannotInferError(msg: String)
      extends Exception(s"cannot infer: $msg")
  final case class ExpectedPiError(msg: String)
      extends Exception(s"expected a pi type: $msg")
  final case class ExpectedSigmaError(msg: String)
      extends Exception(s"expected a sigma type: $msg")
  final case class UndefinedVarError(msg: String)
      extends Exception(s"undefined variable: $msg")
  final case class HoleFoundError(msg: String)
      extends Exception(s"hole found: $msg")
