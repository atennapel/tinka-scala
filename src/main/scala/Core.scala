import Common.*

object Core:
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
  export Level.*

  // terms
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
    case Type(lvl: Level)

    case Pi(bind: Bind, icit: Icit, ty: Ty, u1: Level, body: Ty, u2: Level)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Lam(bind: Bind, icit: Icit, body: Tm)

    case PiLvl(x: Bind, body: Ty, u: Level)
    case AppLvl(fn: Tm, arg: FinLevel)
    case LamLvl(bind: Bind, body: Tm)

    case Sigma(bind: Bind, ty: Ty, u1: Level, body: Ty, u2: Level)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case UnitType
    case Unit

    case Meta(id: MetaId)
    case AppPruning(fn: Tm, spine: Pruning)
    case PostponedCheck(id: PostponeId)

    def appPruning(pr: Pruning): Tm =
      def go(x: Ix, pr: Pruning): Tm = pr match
        case Nil           => this
        case Some(i) :: pr => App(go(x + 1, pr), Var(x), i)
        case None :: pr    => go(x + 1, pr)
      go(ix0, pr)

    override def toString: String = this match
      case Var(ix)             => s"'$ix"
      case Let(x, t, v, b)     => s"(let $x : $t = $v; $b)"
      case Type(LFinLevel(LZ)) => s"Type"
      case Type(lvl)           => s"Type $lvl"
      case Meta(id)            => s"?$id"
      case AppPruning(fn, _)   => s"?*$fn"
      case PostponedCheck(id)  => s"!$id"

      case Pi(x, Impl, t, _, b, _)         => s"({$x : $t} -> $b)"
      case Pi(DoBind(x), Expl, t, _, b, _) => s"(($x : $t) -> $b)"
      case Pi(DontBind, Expl, t, _, b, _)  => s"($t -> $b)"

      case PiLvl(x, b, _) => s"(<$x> -> $b)"
      case LamLvl(x, b)   => s"(\\<$x>. $b)"

      case Sigma(DoBind(x), t, _, b, _) => s"(($x : $t) ** $b)"
      case Sigma(DontBind, t, _, b, _)  => s"($t ** $b)"

      case App(l, r, Expl) => s"($l $r)"
      case App(l, r, Impl) => s"($l {$r})"

      case AppLvl(l, r) => s"($l <$r>)"

      case Lam(x, Expl, b) => s"(\\$x. $b)"
      case Lam(x, Impl, b) => s"(\\{$x}. $b)"

      case Proj(tm, proj) => s"$tm$proj"
      case Pair(fst, snd) => s"($fst, $snd)"
      case UnitType       => "()"
      case Unit           => "[]"
  export Tm.*
