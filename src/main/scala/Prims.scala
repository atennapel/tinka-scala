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
    case PUnitType => "Type 0"
    case PUnit     => "()"

    case PLift     => "<k l> -> Type l -> Type (max l k)"
    case PLiftTerm => "<k l> {A : Type l} -> A -> Lift <k> <l> A"
    case PLower    => "<k l> {A : Type l} -> Lift <k> <l> A -> A"

    case PLabel => "Type 0"

    case PEnum  => "Type 0"
    case PENil  => "Enum"
    case PECons => "Label -> Enum -> Enum"
    case PElimEnum =>
      "<k> (P : Enum -> Type k) (nil : P ENil) (cons : (l : Label) (tl : Enum) -> P tl -> P (ECons l tl)) (e : Enum) -> P e"

    case PTag => "Enum -> Type 0"
    case PTZ  => "{l : Label} {e : Enum} -> Tag (ECons l e)"
    case PTS  => "{l : Label} {e : Enum} -> Tag e -> Tag (ECons l e)"
    case PElimTag =>
      """<k> (P : {e : Enum} -> Tag e -> Type k)
         (z : {l : Label} {e : Enum} -> P {ECons l e} TZ)
         (s : {l : Label} {e : Enum} (t : Tag e) -> P t -> P (TS {l} t))
         {e : Enum} (t : Tag e) -> P t"""

    case PId   => "<l k> {A : Type l} {B : Type k} -> A -> B -> Type 0"
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
