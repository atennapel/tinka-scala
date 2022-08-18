import Common.*

object Surface:
  type Ty = Tm

  enum ArgInfo:
    case ArgNamed(name: Name)
    case ArgIcit(icit: Icit)
  export ArgInfo.*

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

    case Pi(bind: Bind, icit: Icit, ty: Ty, body: Ty)
    case App(fn: Tm, arg: Tm, info: ArgInfo)
    case Lam(bind: Bind, info: ArgInfo, ty: Option[Ty], body: Ty)

    case Sigma(bind: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case UnitType
    case Unit

    case Hole

    case SPos(pos: Pos, tm: Tm)

    override def toString: String = this match
      case SPos(_, tm) => tm.toString

      case Var(x) => s"$x"
      case Type   => "Type"
      case Hole   => "_"

      case Let(x, Some(t), v, b) => s"(let $x : $t = $v; $b)"
      case Let(x, None, v, b)    => s"(let $x = $v; $b)"

      case Pi(x, Impl, t, b)      => s"({$x : $t} -> $b)"
      case Pi(DoBind(x), _, t, b) => s"(($x : $t) -> $b)"
      case Pi(DontBind, _, t, b)  => s"($t -> $b)"

      case Sigma(DoBind(x), t, b) => s"(($x : $t) ** $b)"
      case Sigma(DontBind, t, b)  => s"($t ** $b)"

      case App(l, r, ArgNamed(x))   => s"($l {$x = $r})"
      case App(l, r, ArgIcit(Impl)) => s"($l {$r})"
      case App(l, r, _)             => s"($l $r)"

      case Lam(x, ArgNamed(y), Some(t), b)   => s"(\\{$x : $t = $y}. $b)"
      case Lam(x, ArgIcit(Impl), Some(t), b) => s"(\\{$x : $t}. $b)"
      case Lam(x, _, Some(t), b)             => s"(\\($x : $t). $b)"
      case Lam(x, ArgNamed(y), None, b)      => s"(\\{$x = $y}. $b)"
      case Lam(x, ArgIcit(Impl), None, b)    => s"(\\{$x}. $b)"
      case Lam(x, _, None, b)                => s"(\\$x. $b)"

      case Proj(tm, proj) => s"$tm$proj"
      case Pair(fst, snd) => s"($fst, $snd)"
      case UnitType       => "()"
      case Unit           => "[]"
  export Tm.*
