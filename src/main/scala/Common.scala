object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  opaque type Ix = Int

  extension (i: Ix) def apply[A](xs: List[A]): A = xs(i)

  opaque type Lvl = Int

  val lvl0: Lvl = 0

  extension (l: Lvl)
    def +(o: Int): Lvl = l + o
    def toIx(implicit k: Lvl): Ix = k - l - 1

  type Name = String

  enum Bind:
    case DontBind
    case DoBind(name: Name)
  export Bind.*
