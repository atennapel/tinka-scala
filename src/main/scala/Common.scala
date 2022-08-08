object Common:
  opaque type Ix = Int

  extension (ix: Ix) inline def index[A](e: Seq[A]): A = e(ix)

  opaque type Lvl = Int
  inline def lvl0: Lvl = 0

  extension (lvl: Lvl)
    inline def +(d: Lvl | Int): Lvl = lvl + d
    inline def toIx(implicit k: Lvl): Ix = k - lvl - 1

  opaque type MetaId = Int

  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"

  enum Bind:
    case Bound(name: Name)
    case DontBind

    override def toString: String = this match
      case Bound(x) => x.toString
      case DontBind => "_"
  export Bind.*
