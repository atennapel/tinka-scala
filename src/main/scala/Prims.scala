import Common.*
import Value.*
import Evaluation.*

object Prims:
  private val primTypes: Map[PrimName, Val] = Map(
    PUnitType -> VType,
    PUnitValue -> VUnitType(),
    PVoid -> VType,
    // {A : Type} -> Void -> A
    PAbsurd -> vpiI("A", VType, A => vfun(VVoid(), A)),
    PBool -> VType,
    PTrue -> VBool(),
    PFalse -> VBool(),
    // {A B : Type} -> A -> B -> Type
    PId -> vpiI(
      "A",
      VType,
      A => vpiI("B", VType, B => vfun(A, vfun(B, VType)))
    ),
    // {A : Type} {x : A} -> Id {A} {A} x x
    PRefl -> vpiI("A", VType, A => vpiI("x", A, x => VId(A, A, x, x))),
    // {I : Type} -> ((I -> Type) -> I -> Type) -> I -> Type
    PFix -> vpiI(
      "I",
      VType,
      I => vfun(vfun(vfun(I, VType), vfun(I, VType)), vfun(I, VType))
    ),
    // {I : Type} {F : (I -> Type) -> I -> Type} {i : I} -> F (Fix {I} F) i -> Fix {I} F i
    PRoll -> vpiI(
      "I",
      VType,
      I =>
        vpiI(
          "F",
          vfun(vfun(I, VType), vfun(I, VType)),
          F =>
            vpiI(
              "i",
              I,
              i =>
                vfun(
                  vapp(vapp(F, vlamE("i", i => VFix(I, F, i)), Expl), i, Expl),
                  VFix(I, F, i)
                )
            )
        )
    )
  )

  def primType(x: PrimName): Val = primTypes(x)
