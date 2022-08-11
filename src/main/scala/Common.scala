import scala.annotation.targetName

object Common:
  opaque type Ix = Int

  extension (ix: Ix) inline def index[A](e: Seq[A]): A = e(ix)

  opaque type Lvl = Int
  inline def lvl0: Lvl = 0

  extension (lvl: Lvl)
    inline def +(d: Lvl | Int): Lvl = lvl + d
    inline def toIx(implicit k: Lvl): Ix = k - lvl - 1
    inline def expose: Int = lvl

  opaque type MetaId = Int

  inline def metaId(id: Int): MetaId = id

  extension (id: MetaId)
    @targetName("exposeMetaId")
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

  enum BD:
    case Bound
    case Defined
  export BD.*

  type BDs = List[BD]
