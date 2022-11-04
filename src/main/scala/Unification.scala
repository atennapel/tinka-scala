import Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Syntax.ProjType.*
import Metas.*
import Errors.UnifyError
import Debug.debug

import scala.collection.immutable.IntMap
import scala.util.Try

object Unification:
  private def solve(m: MetaId, sp: Spine, v: Val)(implicit l: Lvl): Unit =
    throw UnifyError(s"meta solving unimplemented")

  private def intersect(m: MetaId, sp1: Spine, sp2: Spine)(implicit
      l: Lvl
  ): Unit = throw UnifyError(s"meta solving unimplemented")

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(implicit
      l: Lvl
  ): Unit = throw UnifyError(s"meta solving unimplemented")

  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError(s"spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit =
    (a, b) match
      case (SId, SId)                       => return ()
      case (SApp(s1, a, _), SApp(s2, b, _)) => unify(s1, s2); unify(a, b)
      case (SAppLvl(a, v1), SAppLvl(b, v2)) => unify(a, b); unify(v1, v2)
      case (SProj(s1, p1), SProj(s2, p2)) if p1 == p2 => unify(s1, s2)
      case (SProj(s1, Fst), SProj(s2, Named(_, n)))   => unifyProj(s1, s2, n)
      case (SProj(s1, Named(_, n)), SProj(s2, Fst))   => unifyProj(s2, s1, n)
      case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos[Val], b: Clos[Val])(implicit l: Lvl): Unit =
    val v = VVar(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  private def unifyClosLvl(a: Clos[VFinLevel], b: Clos[VFinLevel])(implicit
      l: Lvl
  ): Unit =
    val v = VFinLevel.vr(l)
    unify(a.inst(v), b.inst(v))(l + 1)

  private def unify(a: ClosLvl, b: ClosLvl)(implicit k: Lvl): Unit =
    val v = VFinLevel.vr(k)
    unify(a.inst(v), b.inst(v))(k + 1)

  def unify(a: VFinLevel, b: VFinLevel)(implicit l: Lvl): Unit =
    (force(a), force(b)) match
      case (a, b) if a == b => () // TODO: level meta solving
      case (a, b) =>
        throw UnifyError(s"cannot unify fin levels ${quote(a)} ~ ${quote(b)}")

  def unify(a: VLevel, b: VLevel)(implicit l: Lvl): Unit = (a, b) match
    case (VOmega1, VOmega1) => ()
    case (VOmega, VOmega)   => ()
    case (VFL(a), VFL(b))   => unify(a, b)
    case _ => throw UnifyError(s"cannot unify levels ${quote(a)} ~ ${quote(b)}")

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VType(u1), VType(u2)) => unify(u1, u2)
      case (VUnitType, VUnitType) => ()

      case (VPi(_, i1, t1, u11, b1, u12), VPi(_, i2, t2, u21, b2, u22))
          if i1 == i2 =>
        unify(u11, u21); unify(u21, u22); unify(t1, t2); unify(b1, b2)
      case (VSigma(_, t1, u11, b1, u12), VSigma(_, t2, u21, b2, u22)) =>
        unify(u11, u21); unify(u21, u22); unify(t1, t2); unify(b1, b2)
      case (VPiLvl(_, b1, u1), VPiLvl(_, b2, u2)) =>
        unifyClosLvl(b1, b2); unify(u1, u2)

      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VLam(_, i, b), v) =>
        val w = VVar(l); unify(b.inst(w), vapp(v, w, i))(l + 1)
      case (v, VLam(_, i, b)) =>
        val w = VVar(l); unify(vapp(v, w, i), b.inst(w))(l + 1)

      case (VLamLvl(_, b1), VLamLvl(_, b2)) => unifyClosLvl(b1, b2)
      case (VLamLvl(_, b), w) =>
        val v = VFinLevel.vr(l); unify(b.inst(v), vapp(w, v))(l + 1)
      case (w, VLamLvl(_, b)) =>
        val v = VFinLevel.vr(l); unify(vapp(w, v), b.inst(v))(l + 1)

      case (VPair(a1, b1), VPair(a2, b2)) => unify(a1, a2); unify(b1, b2)
      case (VPair(a, b), v) => unify(a, vproj(v, Fst)); unify(b, vproj(v, Snd))
      case (v, VPair(a, b)) => unify(vproj(v, Fst), a); unify(vproj(v, Snd), b)

      case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

      case (VFlex(m1, sp1), VFlex(m2, sp2)) =>
        if m1 == m2 then intersect(m1, sp1, sp2)
        else flexFlex(m1, sp1, m2, sp2)
      case (VFlex(m, sp), v) => solve(m, sp, v)
      case (v, VFlex(m, sp)) => solve(m, sp, v)

      case (VUnitValue, _) => ()
      case (_, VUnitValue) => ()

      case _ => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
