import Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Syntax.ProjType.*
import Metas.*
import Errors.UnifyError
import Debug.debug

import scala.collection.immutable.IntMap
import scala.util.Try

object Unification:
  def unify(a: Val, b: Val)(implicit k: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    ???
