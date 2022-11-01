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

  enum RLevel:
    case RLVar(name: Name)
    case RLS(lvl: RLevel)
    case RLZ
    case RLMax(a: RLevel, b: RLevel)
    case RLHole
    case RLPos(pos: Pos, lvl: RLevel)

    override def toString: String = this match
      case RLVar(x)    => x.toString
      case RLS(l)      => s"(S $l)"
      case RLZ         => s"0"
      case RLMax(a, b) => s"(max $a $b)"
      case RLHole      => s"_"
      case RLPos(_, l) => l.toString
  export RLevel.*

  type RTy = RTm
  enum RTm:
    case RType(lvl: RLevel)
    case RVar(name: Name)
    case RLet(name: Name, ty: Option[RTy], value: RTm, body: RTm)

    case RLam(bind: Bind, info: RArgInfo, ty: Option[RTy], body: RTm)
    case RApp(fn: RTm, arg: RTm, info: RArgInfo)
    case RPi(bind: Bind, icit: Icit, ty: RTy, body: RTy)

    case RPiLvl(name: Bind, body: RTy)
    case RAppLvl(fn: RTm, arg: RLevel, info: Option[Name])
    case RLamLvl(bind: Bind, info: Option[Name], body: RTm)

    case RPair(fst: RTm, snd: RTm)
    case RProj(tm: RTm, proj: RProjType)
    case RSigma(bind: Bind, ty: RTy, body: RTy)

    case RPos(pos: Pos, tm: RTm)
    case RHole(name: Option[Name])

    override def toString: String = this match
      case RType(RLZ)                          => "Type"
      case RType(lvl)                          => s"Type $lvl"
      case RVar(x)                             => s"$x"
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
      case RPiLvl(x, b)                        => s"(<$x> -> $b)"
      case RLamLvl(x, None, b)                 => s"(\\<$x>. $b)"
      case RLamLvl(x, Some(y), b)              => s"(\\<$x = $y>. $b)"
      case RAppLvl(l, r, None)                 => s"($l <$r>)"
      case RAppLvl(l, r, Some(x))              => s"($l <$x = $r>)"
      case RPair(fst, snd)                     => s"($fst, $snd)"
      case RProj(tm, proj)                     => s"$tm$proj"
      case RSigma(x, t, b)                     => s"(($x : $t) ** $b)"
      case RPos(_, tm)                         => tm.toString
      case RHole(x)                            => s"_${x.getOrElse("")}"
  export RTm.*
