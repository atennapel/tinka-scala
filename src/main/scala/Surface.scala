import Common.*

object Surface:
  type Ty = Tm

  enum ProjType:
    case Fst
    case Snd
    case Named(name: Name)

    override def toString: String = this match
      case Fst      => ".1"
      case Snd      => ".2"
      case Named(x) => s".$x"
  export ProjType.*

  enum Tm:
    case Var(name: Name)
    case Let(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Type

    case Pi(bind: Bind, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm)
    case Lam(bind: Bind, ty: Option[Ty], body: Ty)

    case Sigma(bind: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case UnitType
    case Unit

    case Hole

    override def toString: String = this match
      case Var(x)                => s"$x"
      case Type                  => "Type"
      case Hole                  => "_"
      case Let(x, Some(t), v, b) => s"(let $x : $t = $v; $b)"
      case Let(x, None, v, b)    => s"(let $x = $v; $b)"
      case Pi(Bound(x), t, b)    => s"(($x : $t) -> $b)"
      case Pi(DontBind, t, b)    => s"($t -> $b)"
      case Sigma(Bound(x), t, b) => s"(($x : $t) ** $b)"
      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case App(l, r)             => s"($l $r)"
      case Lam(x, Some(t), b)    => s"(\\($x : $t). $b)"
      case Lam(x, None, b)       => s"(\\$x. $b)"
      case Proj(tm, proj)        => s"$tm$proj"
      case Pair(fst, snd)        => s"($fst, $snd)"
      case UnitType              => "()"
      case Unit                  => "[]"
  export Tm.*
