import scala.annotation.tailrec

object Common:
  opaque type Ix = Int
  opaque type Lvl = Int

  def ixEnv[A](env: Seq[A], ix: Ix): A = env(ix)
  def lvlFromEnv[A](env: Seq[A]): Lvl = env.size

  def initialLvl: Lvl = 0
  def initialIx: Ix = 0
  def lvl2ix(l: Lvl, x: Lvl): Ix = l - x - 1
  def lvlInc(l: Lvl): Lvl = l + 1
  def ixInc(ix: Ix): Ix = ix + 1
  def exposeLvl(l: Lvl): Int = l

  type Name = String

  @tailrec
  def freshName(x: Name, ns: Seq[Name]): Name =
    if x == "_" then x
    else if ns.contains(x) then freshName(nextName(x), ns)
    else x

  // TODO: better name generation
  def nextName(x: Name): Name =
    if x == "_" then x
    else s"$x'"

  type MetaId = Int

  def metaId(id: Int): MetaId = id
  def exposeMetaId(ix: MetaId): Int = ix

  enum BD:
    case Bound
    case Defined

  type BDs = List[BD]
