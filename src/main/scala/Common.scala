object Common:
  opaque type Ix = Int

  extension (ix: Ix) def index[A](e: Seq[A]): A = e(ix)

  opaque type Lvl = Int
  val lvl0: Lvl = 0

  extension (lvl: Lvl)
    def +(d: Lvl | Int): Lvl = lvl + d

    def toIx(implicit k: Lvl): Ix = k - lvl - 1

  opaque type MetaId = Int

  opaque type Name = String

  def mkName(x: String): Name = x

  enum Bind:
    case Bound(name: Name)
    case DontBind

    override def toString: String = this match
      case Bound(x) => x.toString
      case DontBind => "_"
  export Bind.*
