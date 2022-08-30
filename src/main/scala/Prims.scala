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
