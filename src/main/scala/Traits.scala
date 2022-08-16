import Common.*
import Value.Val

// some traits to break the mutual dependency between unification and elaboration
trait IUnification:
  def unify(a: Val, b: Val)(implicit k: Lvl): Unit

trait IElaboration:
  def retryPostpone(id: PostponeId): Unit
