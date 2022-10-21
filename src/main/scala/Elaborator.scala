import Presyntax.RTm
import Syntax.{Tm, Ty}

object Elaborator:
  val elab = new Elaboration
  val unif = new Unification(elab)
  elab.setUnification(unif)

  def elaborate(tm: RTm)(implicit ctx: Ctx = Ctx.empty()): (Tm, Ty) =
    elab.elaborate(tm)
