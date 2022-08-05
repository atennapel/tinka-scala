object Common:
  opaque type Ix = Int

  extension (ix: Ix) def index[A](e: Seq[A]): A = e(ix)

  opaque type Lvl = Int

  extension (lvl: Lvl)
    def +(d: Lvl | Int): Lvl = lvl + d

    def toIx(implicit k: Lvl): Ix = k - lvl - 1

  opaque type MetaId = Int

  opaque type Name = String

  enum Bind:
    case Bound(name: Name)
    case DontBind
  export Bind.*
