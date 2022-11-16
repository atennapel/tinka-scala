import Common.*
import Value.*

import scala.collection.mutable

object Prims:
  private val primTypes: mutable.Map[PrimName, (VTy, VLevel)] =
    mutable.Map.empty

  def addPrimType(x: PrimName, ty: VTy, lv: VLevel): Unit =
    primTypes += (x -> (ty, lv))

  def getPrimType(x: PrimName): (VTy, VLevel) = primTypes(x)

  def primTypeScript(x: PrimName): String = x match
    case PVoid   => "Type"
    case PAbsurd => "<l> {A : Type l} -> Void -> A"

    case PUnitType => "Type"
    case PUnit     => "()"

    case PBool  => "Type"
    case PTrue  => "Bool"
    case PFalse => "Bool"
    case PElimBool =>
      "<l> (P : Bool -> Type l) -> P True -> P False -> (b : Bool) -> P b"

    case PLift     => "<k l> -> Type l -> Type (max l k)"
    case PLiftTerm => "<k l> {A : Type l} -> A -> Lift <k> <l> A"
    case PLower    => "<k l> {A : Type l} -> Lift <k> <l> A -> A"

    case PId   => "<l k> {A : Type l} {B : Type k} -> A -> B -> Type"
    case PRefl => "<l> {A : Type l} {x : A} -> Id <l> <l> {A} {A} x x"
    case PElimId =>
      """<k l>
         {A : Type l}
         {x : A}
         (P : {y : A} -> Id <l> <l> {A} {A} x y -> Type k)
         (refl : P {x} Refl)
         {y : A}
         (p : Id <l> <l> {A} {A} x y)
         -> P {y} p"""

    case PSing     => "<l> {A : Type l} -> A -> Type l"
    case PSingCon  => "<l> {A : Type l} (x : A) -> Sing <l> {A} x"
    case PSingElim => "<l> {A : Type l} {x : A} -> Sing <l> {A} x -> A"
