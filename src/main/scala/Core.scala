import Common.*

object Core:
  type Ty = Tm

  enum ProjType:
    case Fst
    case Snd
    case Named(name: Name, ix: Int)

    override def toString: String = this match
      case Fst         => ".1"
      case Snd         => ".2"
      case Named(x, _) => s".$x"
  export ProjType.*

  enum Tm:
    case Var(ix: Ix)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)
    case Type

    case Pi(bind: Bind, icit: Icit, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Lam(bind: Bind, icit: Icit, body: Ty)

    case Sigma(bind: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case UnitType
    case Unit

    case Meta(id: MetaId)
    case AppPruning(fn: Tm, spine: Pruning)

    override def toString: String = this match
      case Var(ix)           => s"'$ix"
      case Let(x, t, v, b)   => s"(let $x : $t = $v; $b)"
      case Type              => "Type"
      case Meta(id)          => s"?$id"
      case AppPruning(fn, _) => s"?*$fn"

      case Pi(x, Impl, t, b)         => s"({$x : $t} -> $b)"
      case Pi(DoBind(x), Expl, t, b) => s"(($x : $t) -> $b)"
      case Pi(DontBind, Expl, t, b)  => s"($t -> $b)"

      case Sigma(DoBind(x), t, b) => s"(($x : $t) ** $b)"
      case Sigma(DontBind, t, b)  => s"($t ** $b)"

      case App(l, r, Expl) => s"($l $r)"
      case App(l, r, Impl) => s"($l {$r})"

      case Lam(x, Expl, b) => s"(\\$x. $b)"
      case Lam(x, Impl, b) => s"(\\{$x}. $b)"

      case Proj(tm, proj) => s"$tm$proj"
      case Pair(fst, snd) => s"($fst, $snd)"
      case UnitType       => "()"
      case Unit           => "[]"
  export Tm.*
