import scala.annotation.targetName

object Common:
  type Pos = (Int, Int) // (line, col)

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

  opaque type LMetaId = Int

  inline def lmetaId(id: Int): LMetaId = id

  extension (id: LMetaId)
    @targetName("exposeLMetaId")
    inline def expose: Int = id

  opaque type PostponeId = Int

  inline def postponeId(id: Int): PostponeId = id

  extension (id: PostponeId)
    @targetName("exposePostponeId")
    inline def expose: Int = id

  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"

    def expose: String = x

  enum Bind:
    case DoBind(name: Name)
    case DontBind

    override def toString: String = this match
      case DoBind(x) => x.toString
      case DontBind  => "_"

    def toName: Name = this match
      case DoBind(x) => x
      case DontBind  => Name("_")
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

  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  // primitives
  enum PrimName:
    case PUnitType
    case PUnit

    case PLift
    case PLiftTerm
    case PLower

    case PLabel

    case PEnum
    case PENil
    case PECons
    case PElimEnum

    case PTag
    case PTZ
    case PTS
    case PElimTag

    case PId
    case PRefl
    case PElimId

    override def toString: String = this match
      case PUnitType => "()"
      case PUnit     => "[]"
      case PLift     => "Lift"
      case PLiftTerm => "lift"
      case PLower    => "lower"
      case PLabel    => "Label"
      case PEnum     => "Enum"
      case PENil     => "ENil"
      case PECons    => "ECons"
      case PElimEnum => "elimEnum"
      case PTag      => "Tag"
      case PTZ       => "TZ"
      case PTS       => "TS"
      case PElimTag  => "elimTag"
      case PId       => "Id"
      case PRefl     => "Refl"
      case PElimId   => "elimId"
  export PrimName.*
  object PrimName:
    def apply(x: Name): Option[PrimName] = x.expose match
      case "()"       => Some(PUnitType)
      case "[]"       => Some(PUnit)
      case "Lift"     => Some(PLift)
      case "lift"     => Some(PLiftTerm)
      case "lower"    => Some(PLower)
      case "Label"    => Some(PLabel)
      case "Enum"     => Some(PEnum)
      case "ENil"     => Some(PENil)
      case "ECons"    => Some(PECons)
      case "elimEnum" => Some(PElimEnum)
      case "Tag"      => Some(PTag)
      case "TZ"       => Some(PTZ)
      case "TS"       => Some(PTS)
      case "elimTag"  => Some(PElimTag)
      case "Id"       => Some(PId)
      case "Refl"     => Some(PRefl)
      case "elimId"   => Some(PElimId)
      case _          => None
