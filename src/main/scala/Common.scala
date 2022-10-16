object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  type Pos = (Int, Int) // (line, col)

  opaque type Ix = Int

  extension (i: Ix) def apply[A](xs: List[A]): A = xs(i)

  opaque type Lvl = Int

  val lvl0: Lvl = 0

  extension (l: Lvl)
    def +(o: Int): Lvl = l + o
    def toIx(implicit k: Lvl): Ix = k - l - 1

  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"
    def expose: String = x

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name("_")
      case DoBind(x) => x
  export Bind.*

  enum Icit:
    case Expl
    case Impl
  export Icit.*
