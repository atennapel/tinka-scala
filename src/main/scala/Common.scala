import scala.annotation.targetName

object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  type Pos = (Int, Int) // (line, col)

  opaque type Ix = Int
  inline def ix0: Ix = 0

  extension (i: Ix)
    inline def expose: Int = i
    inline def apply[A](xs: List[A]): A = xs(i)
    inline def >(o: Int | Ix): Boolean = i > o
    inline def +(o: Int): Ix = i + o

  opaque type Lvl = Int
  inline def lvl0: Lvl = 0

  inline def mkLvl(i: Int): Lvl = i

  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

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
      if x.head.isLetter || x == "[]" || x == "()" then x else s"($x)"
    inline def expose: String = x

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

  type Pruning = List[Option[Icit]]

  opaque type RevPruning = Pruning
  inline def revPruning(p: Pruning): RevPruning = p.reverse
  extension (p: RevPruning) inline def expose: List[Option[Icit]] = p

  // primitives
  trait PrimName
  enum PrimConName extends PrimName:
    case PUnitValue
    case PUnitType

    case PVoid

    case PBool
    case PTrue
    case PFalse

    case PId
    case PRefl

    case PFix
    case PRoll

    override def toString: String = this match
      case PUnitValue => "[]"
      case PUnitType  => "()"

      case PVoid => "Void"

      case PBool  => "Bool"
      case PTrue  => "True"
      case PFalse => "False"

      case PId   => "Id"
      case PRefl => "Refl"

      case PFix  => "Fix"
      case PRoll => "Roll"

  export PrimConName.*
  enum PrimElimName extends PrimName:
    case PAbsurd
    case PElimBool
    case PElimId

    override def toString: String = this match
      case PAbsurd   => "absurd"
      case PElimBool => "elimBool"
      case PElimId   => "elimId"
  export PrimElimName.*

  object PrimName:
    def apply(x: String): Option[Either[PrimElimName, PrimConName]] = x match
      case "[]" => Some(Right(PUnitValue))
      case "()" => Some(Right(PUnitType))

      case "Void"   => Some(Right(PVoid))
      case "absurd" => Some(Left(PAbsurd))

      case "Bool"     => Some(Right(PBool))
      case "True"     => Some(Right(PTrue))
      case "False"    => Some(Right(PFalse))
      case "elimBool" => Some(Left(PElimBool))

      case "Id"     => Some(Right(PId))
      case "Refl"   => Some(Right(PRefl))
      case "elimId" => Some(Left(PElimId))

      case "Fix"  => Some(Right(PFix))
      case "Roll" => Some(Right(PRoll))

      case _ => None

    def apply(x: Name): Option[Either[PrimElimName, PrimConName]] =
      PrimName(x.expose)
