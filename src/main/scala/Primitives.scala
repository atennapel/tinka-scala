import Common.*
import Core.*
import Value.*
import Elaboration.*
import scala.collection.mutable.Map
import scala.collection.immutable.ListMap

object Primitives:
  private val primitives: Map[PrimName, (Tm, Val)] = Map.empty

  def foreachPrimitive(fn: (name: PrimName, defn: String) => (Tm, Val)): Unit =
    primitivesTypes.foreachEntry((name, defn) =>
      primitives.put(name, fn(name, defn))
    )

  def getPrimitive(name: PrimName): Option[(Tm, Val)] = primitives.get(name)

  def isPrimitiveEliminator(name: PrimName): Boolean =
    primitiveElims.contains(name)

  private val primitiveElims =
    Set("absurd", "elimBool", "eqLabel", "elimId", "elimFix")

  private val primitivesTypes = ListMap(
    "()" -> "Type",
    "[]" -> "()",
    "Void" -> "Type",
    "absurd" -> "{A} -> Void -> A",
    "Bool" -> "Type",
    "True" -> "Bool",
    "False" -> "Bool",
    "elimBool" -> "(P : Bool -> Type) (t : P True) (f : P False) (b : Bool) -> P b",
    "Label" -> "Type",
    "eqLabel" -> "Label -> Label -> Bool",
    "Id" -> "{A B} -> A -> B -> Type",
    "Refl" -> "{A} {x : A} -> Id x x",
    "elimId" -> """
      {A : Type} {x : A}
      (P : {y : A} -> Id x y -> Type)
      (refl : P {x} Refl)
      {y : A}
      (p : Id x y)
      -> P p
    """.trim,
    "Fix" -> "(Type -> Type) -> Type",
    "In" -> "{F : Type -> Type} -> F (Fix F) -> Fix F",
    "elimFix" -> """
      {F : Type -> Type}
      (P : Fix F -> Type)
      (alg : ((z : Fix F) -> P z) -> (y : F (Fix F)) -> P (In {F} y))
      (x : Fix F)
      -> P x
    """.trim
  )

  val VPrimLabel = VPrim("Label")
  val VPrimTrue = VPrim("True")
  val VPrimFalse = VPrim("False")
