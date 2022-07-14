import Common.*
import Common.Icit.*
import Errors.*

object Core:
  enum ProjType:
    case Fst
    case Snd
    case Named(name: Option[Name], ix: Int)

    override def toString: String = this match
      case Fst                  => "._1"
      case Snd                  => "._2"
      case Named(Some(name), _) => s"$name"
      case Named(_, i)          => s".$i"

  enum Tm:
    case Var(ix: Ix)
    case Prim(name: PrimName)
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
      case Prim(name)                 => name.toString
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
