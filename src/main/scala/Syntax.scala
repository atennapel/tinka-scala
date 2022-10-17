import Common.*

object Syntax:
  enum ProjType:
    case Fst
    case Snd
    case Named(name: Name, ix: Int)

    override def toString: String = this match
      case Fst         => ".1"
      case Snd         => ".2"
      case Named(x, _) => s".$x"
  export ProjType.*

  type Ty = Tm
  enum Tm:
    case Type
    case Var(ix: Ix)
    case Uri(uri: String)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Lam(bind: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Pi(bind: Bind, icit: Icit, ty: Ty, body: Ty)

    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)
    case Sigma(bind: Bind, ty: Ty, body: Ty)

    case UnitType
    case UnitValue

    override def toString: String = this match
      case Type               => "Type"
      case Var(ix)            => s"'$ix"
      case Uri(uri)           => s"#$uri"
      case Let(x, t, v, b)    => s"(let $x : $t = $v; $b)"
      case Lam(x, Expl, b)    => s"(\\$x. $b)"
      case Lam(x, Impl, b)    => s"(\\{$x}. $b)"
      case App(fn, arg, Expl) => s"($fn $arg)"
      case App(fn, arg, Impl) => s"($fn {$arg})"
      case Pi(x, Expl, t, b)  => s"(($x : $t) -> $b)"
      case Pi(x, Impl, t, b)  => s"({$x : $t} -> $b)"
      case Pair(fst, snd)     => s"($fst, $snd)"
      case Proj(tm, proj)     => s"$tm$proj"
      case Sigma(x, t, b)     => s"(($x : $t) ** $b)"
      case UnitType           => "()"
      case UnitValue          => "[]"
  export Tm.*
