import Surface as S
import Core.{Tm, Ty}

object Elaborator:
  val elab = new Elaboration
  val unif = new Unification(elab)
  elab.setUnification(unif)

  def elaborate(tm: S.Tm): (Tm, Ty) = elab.elaborate(tm)
