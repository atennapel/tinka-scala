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
    Set("absurd", "elimBool", "eqLabel", "elimId", "elimIFix")

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
    "IFix" -> "{I : Type} -> ((I -> Type) -> I -> Type) -> I -> Type",
    "IIn" -> "{I} {F : (I -> Type) -> I -> Type} -> {i : I} -> F (IFix F) i -> IFix F i",
    "elimIFix" -> """
      {I}
      {F : (I -> Type) -> I -> Type}
      (P : {i} -> IFix F i -> Type)
      (alg : ({j} (z : IFix F j) -> P z) -> {i} (y : F (IFix F) i) -> P (IIn {I} {F} y))
      {i}
      (x : IFix F i)
      -> P x
    """.trim
  )

  val VPrimLabel = VPrim("Label")
  val VPrimTrue = VPrim("True")
  val VPrimFalse = VPrim("False")
