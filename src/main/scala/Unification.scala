import Common.*
import Common.PrimName.*
import Value.*
import Value.Val.*
import Value.Elim.*
import Value.Head.*
import Errors.*
import Evaluation.*
import Metas.*
import Core.*
import Core.Tm.*
import Core.ProjType.*
import Debug.debug
import scala.collection.immutable.IntMap

object Unification:
  private type Ren = IntMap[Lvl]
  private final case class PRen(dom: Lvl, cod: Lvl, ren: Ren)

  private def lift(pren: PRen): PRen =
    PRen(
      lvlInc(pren.dom),
      lvlInc(pren.dom),
      pren.ren + (exposeLvl(pren.cod), pren.dom)
    )

  private def invert(l: Lvl, sp: Spine): PRen =
    def go(sp: Spine): (Lvl, Ren) = sp match
      case Nil => (initialLvl, IntMap.empty)
      case EApp(v, _) :: sp =>
        val (dom, ren) = go(sp)
        force(v, false) match
          case VVar(x) if !ren.contains(exposeLvl(x)) =>
            (lvlInc(dom), ren + (exposeLvl(x), dom))
          case VVar(_) => throw UnifyError("duplicate variable in meta spine")
          case _       => throw UnifyError("non-variable in meta spine")
      case _ => throw UnifyError("eliminator in meta spine")
    val (dom, ren) = go(sp)
    PRen(dom, l, ren)

  private def rename(m: MetaId, pren: PRen, v: Val): Tm =
    def goVar(pren: PRen, l: Lvl): Ix = pren.ren.get(exposeLvl(l)) match
      case None    => throw UnifyError(s"var out of scope '$l")
      case Some(x) => lvl2ix(pren.dom, x)

    def goSp(pren: PRen, t: Tm, sp: Spine): Tm = sp match
      case Nil                 => t
      case EApp(u, icit) :: sp => App(goSp(pren, t, sp), go(pren, u), icit)
      case EProj(proj) :: sp   => Proj(goSp(pren, t, sp), proj)

    def goLift(pren: PRen, c: Clos): Tm =
      go(lift(pren), vinst(c, VVar(pren.cod)))

    def go(pren: PRen, t: Val): Tm = force(t, false) match
      case VNe(HMeta(x), sp) if m == x =>
        throw UnifyError(s"occurs check failed ?$x")
      case VNe(HMeta(x), sp)  => goSp(pren, Meta(x), sp)
      case VNe(HVar(x), sp)   => goSp(pren, Var(goVar(pren, x)), sp)
      case VNe(HPrim(x), sp)  => goSp(pren, Prim(x), sp)
      case VGlobal(hd, sp, v) => goSp(pren, Global(hd), sp) // TODO: is this OK?
      case VType              => Type

      case VPi(x, icit, ty, b) => Pi(x, icit, go(pren, ty), goLift(pren, b))
      case VLam(x, icit, b)    => Lam(x, icit, goLift(pren, b))

      case VSigma(x, ty, b) => Sigma(x, go(pren, ty), goLift(pren, b))
      case VPair(fst, snd)  => Pair(go(pren, fst), go(pren, snd))

    go(pren, v)

  private def lams(sp: Spine, body: Tm, ix: Int = 0): Tm = sp match
    case Nil                => body
    case EApp(_, i) :: rest => Lam(s"x$ix", i, lams(rest, body, ix + 1))
    case _                  => throw Impossible()

  private def solve(l: Lvl, id: MetaId, sp: Spine, v: Val): Unit =
    debug(s"solve: ?$id ~ ${quote(l, v)}")
    val pren = invert(l, sp)
    val rhs = rename(id, pren, v)
    val solution = lams(sp.reverse, rhs)
    debug(s"solution: ?$id := $solution")
    solveMeta(id, eval(List.empty, solution), solution)

  private def eqvProj(p1: ProjType, p2: ProjType): Boolean = (p1, p2) match
    case (Named(_, i1), Named(_, i2)) => i1 == i2
    case (Fst, Named(_, 0))           => true
    case (Named(_, 0), Fst)           => true
    case (p1, p2)                     => p1 == p2

  private def unifyElim(l: Lvl, e1: Elim, e2: Elim): Unit = (e1, e2) match
    case (EApp(v1, _), EApp(v2, _))                => unify(l, v1, v2)
    case (EProj(p1), EProj(p2)) if eqvProj(p1, p2) => ()
    case _ => throw UnifyError("spine mismatch")

  private def unifySpProj(l: Lvl, sp1: Spine, sp2: Spine, ix: Int): Unit =
    (sp1, ix) match
      case (sp1, 0)                => unifySp(l, sp1, sp2)
      case (EProj(Snd) :: sp1, ix) => unifySpProj(l, sp1, sp2, ix - 1)
      case _                       => throw UnifyError("spine mismatch")

  private def unifySp(l: Lvl, sp1: Spine, sp2: Spine): Unit = (sp1, sp2) match
    case (Nil, Nil) => ()
    case (EProj(Fst) :: sp1, EProj(Named(j, n)) :: sp2) =>
      unifySpProj(l, sp1, sp2, n)
    case (EProj(Named(j, n)) :: sp1, EProj(Fst) :: sp2) =>
      unifySpProj(l, sp2, sp1, n)
    case (e1 :: sp1, e2 :: sp2) =>
      unifySp(l, sp1, sp2)
      unifyElim(l, e1, e2)
    case _ => throw UnifyError("spine mismatch")

  def unify(l: Lvl, t: Val, u: Val): Unit =
    debug(s"unify: ${quote(l, t)} ~ ${quote(l, u)}")
    (force(t, false), force(u, false)) match
      case (VType, VType) => ()
      case (VPi(_, i, ty1, body1), VPi(_, i2, ty2, body2)) if i == i2 =>
        unify(l, ty1, ty2)
        val v = VVar(l)
        unify(lvlInc(l), vinst(body1, v), vinst(body2, v))
      case (VSigma(_, ty1, body1), VSigma(_, ty2, body2)) =>
        unify(l, ty1, ty2)
        val v = VVar(l)
        unify(lvlInc(l), vinst(body1, v), vinst(body2, v))

      case (VLam(_, _, body1), VLam(_, _, body2)) =>
        val v = VVar(l)
        unify(lvlInc(l), vinst(body1, v), vinst(body2, v))
      case (VLam(_, i, body), w) =>
        val v = VVar(l)
        unify(lvlInc(l), vinst(body, v), vapp(w, v, i))
      case (w, VLam(_, i, body)) =>
        val v = VVar(l)
        unify(lvlInc(l), vapp(w, v, i), vinst(body, v))

      case (VPair(fst1, snd1), VPair(fst2, snd2)) =>
        unify(l, fst1, fst2)
        unify(l, snd1, snd2)
      case (VPair(fst, snd), p) =>
        unify(l, fst, vfst(p))
        unify(l, snd, vsnd(p))
      case (p, VPair(fst, snd)) =>
        unify(l, vfst(p), fst)
        unify(l, vsnd(p), snd)

      case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unifySp(l, sp1, sp2)
      case (VNe(HMeta(id), sp), v)                  => solve(l, id, sp, v)
      case (v, VNe(HMeta(id), sp))                  => solve(l, id, sp, v)

      case (VPrim(PUnit), _) => ()
      case (_, VPrim(PUnit)) => ()

      case (VGlobal(h1, sp1, v1), VGlobal(h2, sp2, v2)) if h1 == h2 =>
        try unifySp(l, sp1, sp2)
        catch case _: UnifyError => unify(l, v1(), v2())
      case (VGlobal(_, _, v1), VGlobal(_, _, v2)) => unify(l, v1(), v2())
      case (VGlobal(_, _, v1), v2)                => unify(l, v1(), v2)
      case (v1, VGlobal(_, _, v2))                => unify(l, v1, v2())

      case _ => throw UnifyError("failed to unify")
