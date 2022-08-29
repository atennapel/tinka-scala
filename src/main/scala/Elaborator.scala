import Surface as S
import Core.{Tm, Ty, Level}

object Elaborator:
  val elab = new Elaboration
  val unif = new Unification(elab)
  elab.setUnification(unif)

  def elaborate(tm: S.Tm): (Tm, Ty, Level) = elab.elaborate(tm)
  def elaborateTop(tm: S.Tm): (Tm, Ty, Level) = elab.elaborateTop(tm)
