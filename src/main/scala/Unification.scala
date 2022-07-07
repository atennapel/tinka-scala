import Common.*
import Value.*
import Value.Val.*
import Value.Elim.*
import Value.Head.*
import Errors.*
import Evaluation.*
import Metas.*
import Core.*
import Core.Tm.*
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
      case EApp(v) :: sp =>
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
      case Nil           => t
      case EApp(u) :: sp => App(goSp(pren, t, sp), go(pren, u))

    def goLift(pren: PRen, c: Clos): Tm =
      go(lift(pren), vinst(c, VVar(pren.cod)))

    def go(pren: PRen, t: Val): Tm = t match
      case VNe(HMeta(x), sp) if m == x =>
        throw UnifyError(s"occurs check failed ?$x")
      case VNe(HMeta(x), sp)  => goSp(pren, Meta(x), sp)
      case VNe(HVar(x), sp)   => goSp(pren, Var(goVar(pren, x)), sp)
      case VGlobal(hd, sp, v) => goSp(pren, Global(hd), sp) // TODO: is this OK?
      case VType              => Type

      case VPi(x, ty, b) => Pi(x, go(pren, ty), goLift(pren, b))
      case VLam(x, b)    => Lam(x, goLift(pren, b))

    go(pren, v)

  private def lams(sp: Spine, body: Tm, ix: Int = 0): Tm = sp match
    case Nil       => body
    case _ :: rest => Lam(s"x$ix", lams(rest, body, ix + 1))

  private def solve(l: Lvl, id: MetaId, sp: Spine, v: Val): Unit =
    // println(s"solve ?$id := ${quote(l, v)}")
    val pren = invert(l, sp)
    val rhs = rename(id, pren, v)
    val solution = lams(sp.reverse, rhs)
    // println(s"solution ?$id := $solution")
    solveMeta(id, eval(List.empty, solution), solution)

  private def unifySp(l: Lvl, sp1: Spine, sp2: Spine): Unit = (sp1, sp2) match
    case (Nil, Nil) => ()
    case (EApp(v1) :: sp1, EApp(v2) :: sp2) =>
      unifySp(l, sp1, sp2)
      unify(l, v1, v2)
    case _ => throw UnifyError("spine mismatch")

  def unify(l: Lvl, t: Val, u: Val): Unit =
    // println(s"unify: ${quote(l, t)} ~ ${quote(l, u)}")
    (force(t, false), force(u, false)) match
      case (VType, VType) => ()
      case (VPi(x1, ty1, body1), VPi(x2, ty2, body2)) =>
        unify(l, ty1, ty2)
        val v = VVar(l)
        unify(lvlInc(l), vinst(body1, v), vinst(body2, v))

      case (VLam(_, body1), VLam(_, body2)) =>
        val v = VVar(l)
        unify(lvlInc(l), vinst(body1, v), vinst(body2, v))
      case (VLam(_, body), w) =>
        val v = VVar(l)
        unify(lvlInc(l), vinst(body, v), vapp(w, v))
      case (w, VLam(_, body)) =>
        val v = VVar(l)
        unify(lvlInc(l), vapp(w, v), vinst(body, v))

      case (VNe(h1, sp1), VNe(h2, sp2)) if h1 == h2 => unifySp(l, sp1, sp2)
      case (VNe(HMeta(id), sp), v)                  => solve(l, id, sp, v)
      case (v, VNe(HMeta(id), sp))                  => solve(l, id, sp, v)

      case (VGlobal(h1, sp1, v1), VGlobal(h2, sp2, v2)) if h1 == h2 =>
        try unifySp(l, sp1, sp2)
        catch case _: UnifyError => unify(l, v1(), v2())
      case (VGlobal(_, _, v1), VGlobal(_, _, v2)) => unify(l, v1(), v2())
      case (VGlobal(_, _, v1), v2)                => unify(l, v1(), v2)
      case (v1, VGlobal(_, _, v2))                => unify(l, v1, v2())

      case _ => throw UnifyError("failed to unify")
