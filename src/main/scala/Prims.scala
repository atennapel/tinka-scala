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
    case PUnitType => "Type"
    case PUnit     => "()"

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

    case PNewtype =>
      "<l k> {A : Type l} (B : A -> Type k) -> A -> Type k"
    case PPack =>
      "<l k> {A : Type l} {B : A -> Type k} {x : A} -> B x -> Newtype {A} B x"
    case PUnpack =>
      "<l k> {A : Type l} {B : A -> Type k} {x : A} -> Newtype {A} B x -> B x"

    case PLabel => "Type"

    case PEnum  => "Type"
    case PENil  => "Enum"
    case PECons => "Label -> Enum -> Enum"
    case PElimEnum =>
      "<k> (P : Enum -> Type k) -> (nil : P ENil) -> (cons : (hd : Label) -> (tl : Enum) -> P tl -> P (ECons hd tl)) -> (e : Enum) -> P e"

    case PTag => "Enum -> Type"
    case PTZ  => "{l : Label} {e : Enum} -> Tag (ECons l e)"
    case PTS  => "{l : Label} {e : Enum} -> Tag e -> Tag (ECons l e)"
    case PElimTag =>
      """<k> (P : {e : Enum} -> (t : Tag e) -> Type k) ->
         (z : {l : Label} {e : Enum} -> P {ECons l e} (TZ {l} {e})) ->
         (s : {l : Label} {e : Enum} (t : Tag e) -> P {e} t -> P {ECons l e} (TS {l} {e} t)) ->
         {e : Enum} -> (t : Tag e) -> P {e} t"""
