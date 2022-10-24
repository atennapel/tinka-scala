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
    // (P : Bool -> Type) -> P True -> P False -> (b : Bool) -> P b
    PElimBool -> vpiE(
      "P",
      vfun(VBool(), VType),
      P =>
        vfun(
          vapp(P, VTrue(), Expl),
          vfun(
            vapp(P, VFalse(), Expl),
            vpiE("b", VBool(), b => vapp(P, b, Expl))
          )
        )
    ),
    // {A B : Type} -> A -> B -> Type
    PId -> vpiI(
      "A",
      VType,
      A => vpiI("B", VType, B => vfun(A, vfun(B, VType)))
    ),
    // {A : Type} {x : A} -> Id {A} {A} x x
    PRefl -> vpiI("A", VType, A => vpiI("x", A, x => VId(A, A, x, x))),
    /*
    {A : Type} {x : A}
      (P : {y : A} -> Id x y -> Type)
      (refl : P {x} Refl)
      {y : A}
      (p : Id x y)
      -> P p
     */
    PElimId ->
      vpiI(
        "A",
        VType,
        A =>
          vpiI(
            "x",
            A,
            x =>
              vpiE(
                "P",
                vpiI("y", A, y => vfun(VId(A, A, x, y), VType)),
                P =>
                  vfun(
                    vapp(vapp(P, x, Impl), VRefl(A, x), Expl),
                    vpiI(
                      "y",
                      A,
                      y =>
                        vpiE(
                          "p",
                          VId(A, A, x, y),
                          p => vapp(vapp(P, y, Impl), p, Expl)
                        )
                    )
                  )
              )
          )
      ),
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
    ),
    /* {I : Type} {F : (I -> Type) -> I -> Type}
        (P : {i : I} -> Fix {I} F i -> Type) ->
        (({i: I} (x : Fix {I} {F} i) -> P {i} x) -> {i : I} (x : F (Fix {I} F) i) -> P {i} (Roll {I} {F} {i} x))
        -> {i : I} (x : Fix {I} F i) -> P {i} x
     */
    PElimFix ->
      vpiI(
        "I",
        VType,
        I =>
          vpiI(
            "F",
            vfun(vfun(I, VType), vfun(I, VType)),
            F =>
              vpiE(
                "P",
                vpiI("i", I, i => vfun(VFix(I, F, i), VType)),
                P =>
                  vfun(
                    vfun(
                      vpiI(
                        "i",
                        I,
                        i =>
                          vpiE(
                            "x",
                            VFix(I, F, i),
                            x => vapp(vapp(P, i, Impl), x, Expl)
                          )
                      ),
                      vpiI(
                        "i",
                        I,
                        i =>
                          vpiE(
                            "x",
                            vapp(
                              vapp(F, vlamE("i", i => VFix(I, F, i)), Expl),
                              i,
                              Expl
                            ),
                            x => vapp(vapp(P, i, Impl), VRoll(I, F, i, x), Expl)
                          )
                      )
                    ),
                    vpiI(
                      "i",
                      I,
                      i =>
                        vpiE(
                          "x",
                          VFix(I, F, i),
                          x => vapp(vapp(P, i, Impl), x, Expl)
                        )
                    )
                  )
              )
          )
      )
  )

  def primType(x: PrimName): Val = primTypes(x)
