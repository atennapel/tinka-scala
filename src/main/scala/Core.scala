import Common.*
import Common.Icit.*
import scala.annotation.tailrec
import scala.collection.mutable.StringBuilder
import Errors.*

object Core:
  enum ProjType:
    case Fst
    case Snd

    override def toString: String = this match
      case Fst => "._1"
      case Snd => "._2"

  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Tm, value: Tm, body: Tm)
    case Type

    case Pi(name: Name, icit: Icit, ty: Tm, body: Tm)
    case Lam(name: Name, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)

    case Sigma(name: Name, ty: Tm, body: Tm)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case Meta(id: MetaId)
    case InsertedMeta(id: MetaId, bds: BDs)

    override def toString: String = this match
      case Var(ix)                    => s"'$ix"
      case Global(name)               => name
      case Let(name, ty, value, body) => s"(let $name : $ty = $value; $body)"
      case Type                       => "Type"

      case Pi(x, Expl, ty, b) => s"(($x : $ty) -> $b)"
      case Pi(x, Impl, ty, b) => s"({$x : $ty} -> $b)"
      case Lam(x, Expl, b)    => s"(\\$x. $b)"
      case Lam(x, Impl, b)    => s"(\\{$x}. $b)"
      case App(fn, arg, Expl) => s"($fn $arg)"
      case App(fn, arg, Impl) => s"($fn {$arg})"

      case Sigma(x, ty, b) => s"(($x : $ty) ** $b)"
      case Pair(fst, snd)  => s"($fst, $snd)"
      case Proj(tm, proj)  => s"$tm$proj"

      case Meta(id)            => s"?$id"
      case InsertedMeta(id, _) => s"?$id"
