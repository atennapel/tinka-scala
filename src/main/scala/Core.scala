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
      case Named(Some(name), i) => s".$name"
      case Named(_, i)          => s".$i"

  enum Tm:
    case Var(ix: Ix)
    case Prim(name: PrimName)
    case Global(name: Name)
    case LabelLit(name: Name)
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
      case LabelLit(name)             => s"'$name"
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

    def shift(i: Int, c: Int = 0): Tm = this match
      case Var(ix) =>
        if exposeIx(ix) < c then this else Var(mkIx(exposeIx(ix) + i))
      case Prim(name)     => this
      case Global(name)   => this
      case LabelLit(name) => this
      case Let(name, ty, value, body) =>
        Let(name, ty.shift(i, c), value.shift(i, c), body.shift(i, c + 1))
      case Type => this

      case Pi(x, icit, ty, b) => Pi(x, icit, ty.shift(i, c), b.shift(i, c + 1))
      case Lam(x, icit, b)    => Lam(x, icit, b.shift(i, c + 1))
      case App(fn, arg, icit) => App(fn.shift(i, c), arg.shift(i, c), icit)

      case Sigma(x, ty, b) => Sigma(x, ty.shift(i, c), b.shift(i, c + 1))
      case Pair(fst, snd)  => Pair(fst.shift(i, c), snd.shift(i, c))
      case Proj(tm, proj)  => Proj(tm.shift(i, c), proj)

      case Meta(id)            => this
      case InsertedMeta(id, _) => this
