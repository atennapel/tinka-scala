import Common.Pos

object Errors:
  object Impossible extends Exception("impossible")

  final case class UnifyError(msg: String)
      extends Exception(s"unify error: $msg")

  sealed trait ElabError extends Exception:
    def pos: Pos
  final case class ElabUnifyError(msg: String, pos: Pos)
      extends Exception(s"unify error: $msg")
      with ElabError
  final case class CannotInferError(msg: String, pos: Pos)
      extends Exception(s"cannot infer: $msg")
      with ElabError
  final case class ExpectedSigmaError(msg: String, pos: Pos)
      extends Exception(s"expected a sigma type: $msg")
      with ElabError
  final case class UndefinedVarError(msg: String, pos: Pos)
      extends Exception(s"undefined variable: $msg")
      with ElabError
  final case class HoleFoundError(msg: String, pos: Pos)
      extends Exception(s"hole found: $msg")
      with ElabError
  final case class NamedImplicitError(msg: String, pos: Pos)
      extends Exception(s"named implicit: $msg")
      with ElabError
  final case class IcitMismatchError(msg: String, pos: Pos)
      extends Exception(s"icit mismatch: $msg")
      with ElabError
  final case class UnsolvedMetasError(msg: String, pos: Pos)
      extends Exception(s"unsolved metas: $msg")
      with ElabError
