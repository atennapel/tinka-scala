import scala.annotation.targetName

object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  type Pos = (Int, Int) // (line, col)

  // indeces
  opaque type Ix = Int
  inline def ix0: Ix = 0

  inline def mkIx(i: Int): Ix = i

  extension (i: Ix)
    inline def expose: Int = i
    inline def >(o: Int | Ix): Boolean = i > o
    inline def +(o: Int): Ix = i + o

  // levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0

  inline def mkLvl(i: Int): Lvl = i

  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

  // metas
  opaque type MetaId = Int

  inline def metaId(id: Int): MetaId = id

  extension (id: MetaId)
    @targetName("exposeMetaId")
    inline def expose: Int = id

  // level metas
  opaque type LMetaId = Int

  inline def lmetaId(id: Int): LMetaId = id

  extension (id: LMetaId)
    @targetName("exposeLMetaId")
    inline def expose: Int = id

  // names
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

  // icits
  enum Icit:
    case Expl
    case Impl
  export Icit.*

  // pruning
  type Pruning = List[Option[Icit]]

  opaque type RevPruning = Pruning
  inline def revPruning(p: Pruning): RevPruning = p.reverse
  extension (p: RevPruning) inline def expose: List[Option[Icit]] = p
