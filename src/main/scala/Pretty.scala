import Core.{Tm as CTm}
import Core.Tm as C
import Core.ProjType as CP
import Surface.*
import Surface.Tm.*
import Surface.ProjType.*
import Common.*
import Common.Icit.*

object Pretty:
  private def prettyProjType(tm: Tm, proj: CP): Tm = proj match
    case CP.Fst                  => Proj(tm, Fst)
    case CP.Snd                  => Proj(tm, Snd)
    case CP.Named(Some(name), _) => Proj(tm, Named(name))
    case CP.Named(None, 0)       => Proj(tm, Fst)
    case CP.Named(None, i) =>
      prettyProjType(Proj(tm, Snd), CP.Named(None, i - 1))

  private def prettyTm(tm: CTm, ns: List[Name], hia: Boolean): Tm =
    tm match
      case C.Var(ix)                   => Var(ixEnv(ns, ix))
      case C.Prim(name)                => Var(name.toString)
      case C.Global(name)              => Var(name)
      case C.App(fn, arg, Impl) if hia => prettyTm(fn, ns, hia)
      case C.App(fn, arg, i) =>
        App(prettyTm(fn, ns, hia), prettyTm(arg, ns, hia), Right(i))
      case C.Type                => Type
      case C.LabelLit(x)         => LabelLit(x)
      case C.Meta(id)            => Var(s"?$id")
      case C.InsertedMeta(id, _) => Var(s"?$id")
      case C.Let(x0, ty, value, b) =>
        val x = freshName(x0, ns)
        Let(
          x,
          Some(prettyTm(ty, ns, hia)),
          prettyTm(value, ns, hia),
          prettyTm(b, x :: ns, hia)
        )
      case C.Pi(x0, i, ty, b) =>
        val x = freshName(x0, ns)
        Pi(x, i, prettyTm(ty, ns, hia), prettyTm(b, x :: ns, hia))
      case C.Lam(x0, i, b) =>
        val x = freshName(x0, ns)
        Lam(x, Right(i), None, prettyTm(b, x :: ns, hia))
      case C.Sigma(x0, ty, b) =>
        val x = freshName(x0, ns)
        Sigma(x, prettyTm(ty, ns, hia), prettyTm(b, x :: ns, hia))
      case C.Pair(fst, snd) =>
        Pair(prettyTm(fst, ns, hia), prettyTm(snd, ns, hia))
      case C.Proj(tm, proj) => prettyProjType(prettyTm(tm, ns, hia), proj)

  def pretty(
      tm: CTm,
      ns: List[Name] = Nil,
      hideImplicitApps: Boolean = false
  ): String =
    prettyTm(tm, ns, hideImplicitApps).toString
