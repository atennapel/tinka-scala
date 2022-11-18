import scala.annotation.targetName
import scala.annotation.tailrec

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

    def isInstance: Boolean = x.startsWith("instance") && x.size > 8

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name("_")
      case DoBind(x) => x

    def toSet: Set[Name] = this match
      case DontBind  => Set.empty
      case DoBind(x) => Set(x)

    def isInstance: Boolean = this match
      case DoBind(x) => x.isInstance
      case _         => false
  export Bind.*

  @tailrec
  def fresh(x: Name)(implicit ns: List[Name]): Name =
    if ns.contains(x) then fresh(Name(s"${x}'"))(ns) else x
  def fresh(b: Bind)(implicit ns: List[Name]): Bind = b match
    case DoBind(x) => DoBind(fresh(x))
    case DontBind  => DontBind

  // icits
  enum ImplMode:
    case Unif
    case Inst
  export ImplMode.*

  enum Icit:
    case Expl
    case Impl(impl: ImplMode)
  export Icit.*

  // pruning
  type Pruning = List[Option[Icit]]

  opaque type RevPruning = Pruning
  inline def revPruning(p: Pruning): RevPruning = p.reverse
  extension (p: RevPruning) inline def expose: List[Option[Icit]] = p

  // primitives
  enum PrimName:
    case PLift
    case PLiftTerm
    case PLower

    case PVoid
    case PAbsurd

    case PUnitType
    case PUnit

    case PBool
    case PTrue
    case PFalse
    case PElimBool

    case PId
    case PRefl
    case PElimId

    case PSing
    case PSingCon
    case PSingElim

    case PNewtype
    case PPack
    case PUnpack

    override def toString: String = this match
      case PUnitType => "()"
      case PUnit     => "[]"
      case PLift     => "Lift"
      case PLiftTerm => "lift"
      case PLower    => "lower"
      case PBool     => "Bool"
      case PTrue     => "True"
      case PFalse    => "False"
      case PElimBool => "elimBool"
      case PVoid     => "Void"
      case PAbsurd   => "absurd"
      case PId       => "Id"
      case PRefl     => "Refl"
      case PElimId   => "elimId"
      case PSing     => "Sing"
      case PSingCon  => "sing"
      case PSingElim => "unsing"
      case PNewtype  => "Newtype"
      case PPack     => "pack"
      case PUnpack   => "unpack"
  export PrimName.*
  object PrimName:
    def apply(x: Name): Option[PrimName] = x.expose match
      case "()"       => Some(PUnitType)
      case "[]"       => Some(PUnit)
      case "Lift"     => Some(PLift)
      case "lift"     => Some(PLiftTerm)
      case "lower"    => Some(PLower)
      case "Bool"     => Some(PBool)
      case "True"     => Some(PTrue)
      case "False"    => Some(PFalse)
      case "elimBool" => Some(PElimBool)
      case "Void"     => Some(PVoid)
      case "absurd"   => Some(PAbsurd)
      case "Id"       => Some(PId)
      case "Refl"     => Some(PRefl)
      case "elimId"   => Some(PElimId)
      case "Sing"     => Some(PSing)
      case "sing"     => Some(PSingCon)
      case "unsing"   => Some(PSingElim)
      case "Newtype"  => Some(PNewtype)
      case "pack"     => Some(PPack)
      case "unpack"   => Some(PUnpack)
      case _          => None
