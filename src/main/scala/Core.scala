import Common.*

object Core:
  type Ty = Tm

  enum Tm:
    case Var(ix: Ix)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)
    case Type

    case Pi(bind: Bind, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm)
    case Lam(bind: Bind, body: Ty)

    case Sigma(bind: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)

    case UnitType
    case Unit

    override def toString: String = this match
      case Var(ix)               => s"'$ix"
      case Let(x, t, v, b)       => s"(let $x : $t = $v; $b)"
      case Type                  => "Type"
      case Pi(Bound(x), t, b)    => s"(($x : $t) -> $b)"
      case Pi(DontBind, t, b)    => s"($t -> $b)"
      case Sigma(Bound(x), t, b) => s"(($x : $t) ** $b)"
      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case App(l, r)             => s"($l $r)"
      case Lam(x, b)             => s"(\\$x. $b)"
      case Pair(fst, snd)        => s"($fst, $snd)"
      case UnitType              => "()"
      case Unit                  => "[]"
  export Tm.*
