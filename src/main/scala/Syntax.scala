import Common.*

object Syntax:
  // universe levels
  enum FinLevel:
    case LVar(ix: Ix)
    case LZ
    case LS(lvl: FinLevel)
    case LMax(a: FinLevel, b: FinLevel)
    case LMeta(id: LMetaId)

    private def tryNat: Option[Int] = this match
      case LZ    => Some(0)
      case LS(l) => l.tryNat.map(_ + 1)
      case _     => None

    override def toString: String = this match
      case LVar(i) => s"'$i"
      case LZ      => "0"
      case LS(l)   => l.tryNat.map(n => (n + 1).toString).getOrElse(s"(S $l)")
      case LMax(a, b) => s"(max $a $b)"
      case LMeta(id)  => s"?l$id"

    def +(o: Int): FinLevel =
      var c: FinLevel = this
      for (_ <- 0 until o) c = LS(c)
      c

    def max(o: FinLevel): FinLevel = (this, o) match
      case (LZ, x)        => x
      case (x, LZ)        => x
      case (LS(a), LS(b)) => LS(a max b)
      case (a, b)         => LMax(a, b)

    def shift(d: Int): FinLevel = this match
      case LVar(i)    => LVar(i + d)
      case LS(l)      => LS(l.shift(d))
      case LMax(a, b) => LMax(a.shift(d), b.shift(d))
      case l          => l
  export FinLevel.*

  enum Level:
    case LOmega
    case LOmega1
    case LFinLevel(lvl: FinLevel)

    override def toString: String = this match
      case LOmega       => "omega"
      case LOmega1      => "omega1"
      case LFinLevel(l) => l.toString

    def max(o: Level): Level = (this, o) match
      case (LOmega1, _)                 => LOmega1
      case (_, LOmega1)                 => LOmega1
      case (LOmega, _)                  => LOmega
      case (_, LOmega)                  => LOmega
      case (LFinLevel(a), LFinLevel(b)) => LFinLevel(a max b)

    def shift(d: Int): Level = this match
      case LFinLevel(a) => LFinLevel(a.shift(d))
      case l            => l
  export Level.*

  // terms
  enum ProjType:
    case Fst
    case Snd
    case Named(name: Option[Name], ix: Int)

    override def toString: String = this match
      case Fst               => ".1"
      case Snd               => ".2"
      case Named(Some(x), _) => s".$x"
      case Named(None, i)    => s".$i"
  export ProjType.*

  type Ty = Tm
  enum Tm:
    case Type(lvl: Level)
    case Var(ix: Ix)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Lam(bind: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Pi(bind: Bind, icit: Icit, ty: Ty, u1: Level, body: Ty, u2: Level)

    case AppLvl(fn: Tm, arg: FinLevel)
    case LamLvl(bind: Bind, body: Tm)
    case PiLvl(x: Bind, body: Ty, u: Level)

    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)
    case Sigma(bind: Bind, ty: Ty, u1: Level, body: Ty, u2: Level)

    case UnitType
    case UnitValue

    case Wk(tm: Tm)

    case Meta(id: MetaId)
    case AppPruning(tm: Tm, spine: Pruning)

    def appPruning(pr: Pruning): Tm =
      def go(x: Ix, pr: Pruning): Tm = pr match
        case Nil           => this
        case Some(i) :: pr => App(go(x + 1, pr), Var(x), i)
        case None :: pr    => go(x + 1, pr)
      go(ix0, pr)

    override def toString: String = this match
      case Type(LFinLevel(LZ))     => s"Type"
      case Type(lvl)               => s"Type $lvl"
      case Var(ix)                 => s"'$ix"
      case Let(x, t, v, b)         => s"(let $x : $t = $v; $b)"
      case Lam(x, Expl, b)         => s"(\\$x. $b)"
      case Lam(x, Impl, b)         => s"(\\{$x}. $b)"
      case App(fn, arg, Expl)      => s"($fn $arg)"
      case App(fn, arg, Impl)      => s"($fn {$arg})"
      case AppLvl(l, r)            => s"($l <$r>)"
      case Pi(x, Expl, t, _, b, _) => s"(($x : $t) -> $b)"
      case Pi(x, Impl, t, _, b, _) => s"({$x : $t} -> $b)"
      case PiLvl(x, b, u)          => s"(<$x> -> $b)"
      case LamLvl(x, b)            => s"(\\<$x>. $b)"
      case Pair(fst, snd)          => s"($fst, $snd)"
      case Proj(tm, proj)          => s"$tm$proj"
      case Sigma(x, t, _, b, _)    => s"(($x : $t) ** $b)"
      case UnitType                => s"()"
      case UnitValue               => s"[]"
      case Wk(tm)                  => s"(Wk $tm)"
      case Meta(id)                => s"?$id"
      case AppPruning(tm, spine)   => s"?*$tm"
  export Tm.*
