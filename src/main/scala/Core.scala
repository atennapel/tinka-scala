import Common.*
import scala.annotation.tailrec
import scala.collection.mutable.StringBuilder
import Errors.*

object Core:
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Tm, value: Tm, body: Tm)
    case Type

    case Pi(name: Name, ty: Tm, body: Tm)
    case Lam(name: Name, body: Tm)
    case App(fn: Tm, arg: Tm)

    override def toString: String = this match
      case Var(ix)                    => s"'$ix"
      case Global(name)               => name
      case Let(name, ty, value, body) => s"(let $name : $ty = $value; $body)"
      case Type                       => "Type"

      case Pi(x, ty, b) => s"(($x : $ty) -> $b)"
      case Lam(x, b)    => s"(\\$x. $b)"
      case App(fn, arg) => s"($fn $arg)"
