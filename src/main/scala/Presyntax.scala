import Common.*

object Presyntax:
  enum RArgInfo:
    case RArgNamed(name: Name)
    case RArgIcit(icit: Icit)
  export RArgInfo.*

  enum RProjType:
    case RFst
    case RSnd
    case RNamed(name: Name)

    override def toString: String = this match
      case RFst      => ".1"
      case RSnd      => ".2"
      case RNamed(x) => s".$x"
  export RProjType.*

  type RTy = RTm
  enum RTm:
    case RType
    case RVar(name: Name)
    case RUri(uri: String)
    case RLet(name: Name, ty: Option[RTy], value: RTm, body: RTm)

    case RLam(bind: Bind, info: RArgInfo, ty: Option[RTy], body: RTm)
    case RApp(fn: RTm, arg: RTm, info: RArgInfo)
    case RPi(bind: Bind, icit: Icit, ty: RTy, body: RTy)

    case RPair(fst: RTm, snd: RTm)
    case RProj(tm: RTm, proj: RProjType)
    case RSigma(bind: Bind, ty: RTy, body: RTy)

    case RUnitType
    case RUnitValue

    case RPos(pos: Pos, tm: RTm)
    case RHole(name: Option[Name])

    def uris: Set[String] = this match
      case RUri(uri) => Set(uri)
      case RLet(_, t, v, b) =>
        t.map(_.uris).getOrElse(Set.empty) ++ v.uris ++ b.uris
      case RLam(_, _, t, b) => t.map(_.uris).getOrElse(Set.empty) ++ b.uris
      case RApp(fn, arg, _) => fn.uris ++ arg.uris
      case RPi(_, _, t, b)  => t.uris ++ b.uris
      case RPair(fst, snd)  => fst.uris ++ snd.uris
      case RProj(t, _)      => t.uris
      case RSigma(_, t, b)  => t.uris ++ b.uris
      case RPos(_, t)       => t.uris
      case _                => Set.empty

    override def toString: String = this match
      case RType                               => "Type"
      case RVar(x)                             => s"$x"
      case RUri(uri)                           => s"#$uri"
      case RLet(x, Some(t), v, b)              => s"(let $x : $t = $v; $b)"
      case RLet(x, None, v, b)                 => s"(let $x = $v; $b)"
      case RLam(x, RArgIcit(Expl), Some(t), b) => s"(\\($x : $t). $b)"
      case RLam(x, RArgIcit(Expl), None, b)    => s"(\\$x. $b)"
      case RLam(x, RArgIcit(Impl), Some(t), b) => s"(\\{$x : $t}. $b)"
      case RLam(x, RArgIcit(Impl), None, b)    => s"(\\{$x}. $b)"
      case RLam(x, RArgNamed(y), Some(t), b)   => s"(\\{$x : $t = $y}. $b)"
      case RLam(x, RArgNamed(y), None, b)      => s"(\\{$x = $y}. $b)"
      case RApp(fn, arg, RArgIcit(Expl))       => s"($fn $arg)"
      case RApp(fn, arg, RArgIcit(Impl))       => s"($fn {$arg})"
      case RApp(fn, arg, RArgNamed(y))         => s"($fn {$y = $arg})"
      case RPi(x, Expl, t, b)                  => s"(($x : $t) -> $b)"
      case RPi(x, Impl, t, b)                  => s"({$x : $t} -> $b)"
      case RPair(fst, snd)                     => s"($fst, $snd)"
      case RProj(tm, proj)                     => s"$tm$proj"
      case RSigma(x, t, b)                     => s"(($x : $t) ** $b)"
      case RUnitType                           => "()"
      case RUnitValue                          => "[]"
      case RPos(_, tm)                         => tm.toString
      case RHole(x)                            => s"_${x.getOrElse("")}"
  export RTm.*
