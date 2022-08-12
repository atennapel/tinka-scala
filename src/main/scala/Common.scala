import scala.annotation.targetName

object Common:
  opaque type Ix = Int
  inline def ix0: Ix = 0

  extension (ix: Ix)
    inline def index[A](e: Seq[A]): A = e(ix)
    inline def +(d: Ix | Int): Ix = ix + d

  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(k: Int): Lvl = k

  extension (lvl: Lvl)
    @targetName("addLvl")
    inline def +(d: Lvl | Int): Lvl = lvl + d
    inline def toIx(implicit k: Lvl): Ix = k - lvl - 1
    inline def expose: Int = lvl

  opaque type MetaId = Int

  inline def metaId(id: Int): MetaId = id

  extension (id: MetaId)
    @targetName("exposeMetaId")
    inline def expose: Int = id

  opaque type CheckId = Int

  inline def checkId(id: Int): CheckId = id

  extension (id: CheckId)
    @targetName("exposeCheckId")
    inline def expose: Int = id

  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"

  enum Bind:
    case DoBind(name: Name)
    case DontBind

    override def toString: String = this match
      case DoBind(x) => x.toString
      case DontBind  => "_"
  export Bind.*

  enum Icit:
    case Expl
    case Impl
  export Icit.*

  // pruning
  type Pruning = List[Option[Icit]]

  opaque type RevPruning = Pruning
  inline def revPruning(p: Pruning): RevPruning = p.reverse
  extension (p: RevPruning) inline def expose: List[Option[Icit]] = p
