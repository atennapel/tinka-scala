object Common:
  opaque type Ix = Int
  opaque type Lvl = Int
  type Name = String

  def ixEnv[A](env: Seq[A], ix: Ix): A = env(ix)
  def lvlFromEnv[A](env: Seq[A]): Lvl = env.size

  def initialLvl: Lvl = 0
  def initialIx: Ix = 0
  def lvl2ix(l: Lvl, x: Lvl): Ix = l - x - 1
  def lvlInc(l: Lvl): Lvl = l + 1
  def ixInc(ix: Ix): Ix = ix + 1
