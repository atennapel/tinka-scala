import Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.getGlobal
import Debug.debug

object Evaluation:
  extension (c: Clos[Val])
    def inst(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(EVal(env, v))
      case CFun(fn)       => fn(v)

  extension (c: Clos[VFinLevel])
    def inst(v: VFinLevel): Val = c match
      case CClos(env, tm) => eval(tm)(ELevel(env, v))
      case CFun(fn)       => fn(v)

  extension (c: ClosLvl)
    def inst(v: VFinLevel): VLevel = eval(c.tm)(ELevel(c.env, v))

  // evaluation
  def vapp(fn: Val, arg: Val, icit: Icit): Val = fn match
    case VLam(_, _, b)  => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, arg, icit))
    case VFlex(hd, sp)  => VFlex(hd, SApp(sp, arg, icit))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SApp(sp, arg, icit), () => vapp(v(), arg, icit))
    case _ => impossible()

  def vapp(fn: Val, arg: VFinLevel): Val = fn match
    case VLamLvl(_, b)  => b.inst(arg)
    case VRigid(hd, sp) => VRigid(hd, SAppLvl(sp, arg))
    case VFlex(hd, sp)  => VFlex(hd, SAppLvl(sp, arg))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SAppLvl(sp, arg), () => vapp(v(), arg))
    case _ => impossible()

  def vproj(tm: Val, proj: ProjType): Val = tm match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp) => VRigid(hd, SProj(sp, proj))
    case VFlex(hd, sp)  => VFlex(hd, SProj(sp, proj))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SProj(sp, proj), () => vproj(v(), proj))
    case _ => impossible()

  def vprimelim(
      x: PrimName,
      args: List[Either[VFinLevel, (Val, Icit)]],
      v: Val
  ): Val =
    (x, force(v), args) match
      // lower <k> <l> {A} (lift <k> <l> {A} t) ~> t
      case (PLower, VLiftTerm(_, _, _, t), _) => t

      // unsing <l> {A} {x} (sing <l> {A} x) ~> x
      case (PSingElim, VSingCon(_, _, x), _) => x

      // unsing <l> {A} {x} s ~> x
      case (PSingElim, _, List(_, _, Right((x, _)))) => x

      // unpack <l k> {A} {B} {x} (pack <l k> {A} {B} {x} t) ~> t
      case (PUnpack, VPack(_, _, _, _, _, t), _) => t

      // elimId <k> <l> {A} {x} P refl {y} (Refl <l> {A} {y}) ~> refl
      case (
            PElimId,
            VRefl(_, _, _),
            List(_, _, _, _, _, Right((refl, _)), _)
          ) =>
        refl

      // elimEnum <k> P nil cons ENil ~> nil
      case (PElimEnum, VENil(), List(_, _, Right((nil, _)), _)) => nil
      // elimEnum <k> P nil cons (ECons hd tl) ~> cons hd tl (elimEnum <k> P nil cons tl)
      case (PElimEnum, VECons(hd, tl), List(_, _, _, Right((cons, _)))) =>
        vapp(
          vapp(vapp(cons, hd, Expl), tl, Expl),
          vprimelim(PElimEnum, args, tl),
          Expl
        )

      // elimTag <k> P z s {_} (TZ {l} {e}) ~> z {l} {e}
      case (PElimTag, VTZ(l, e), List(_, _, Right((z, _)), _, _)) =>
        vapp(vapp(z, l, Impl(Unif)), e, Impl(Unif))
      // elimTag <k> P z s {_} (TS {l} {e} t) ~> s {l} {e} t (elimTag <k> P z s {e} t)
      case (PElimTag, VTS(l, e, t), List(_, _, _, Right((s, _)), _)) =>
        vapp(
          vapp(vapp(vapp(s, l, Impl(Unif)), e, Impl(Unif)), t, Expl),
          vprimelim(PElimTag, args.init ++ List(Right((e, Impl(Unif)))), t),
          Expl
        )

      case (_, VRigid(hd, sp), _) => VRigid(hd, SPrim(sp, x, args))
      case (_, VFlex(hd, sp), _)  => VFlex(hd, SPrim(sp, x, args))
      case (_, VGlobal(uri, sp, v), _) =>
        VGlobal(uri, SPrim(sp, x, args), () => vprimelim(x, args, v()))
      case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId                => v
    case SApp(sp, a, i)     => vapp(vspine(v, sp), a, i)
    case SAppLvl(sp, a)     => vapp(vspine(v, sp), a)
    case SProj(sp, proj)    => vproj(vspine(v, sp), proj)
    case SPrim(sp, x, args) => vprimelim(x, args, vspine(v, sp))

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_)     => VMeta(id)

  def vlmeta(id: LMetaId): VFinLevel = getLMeta(id) match
    case LSolved(_, v) => v // TODO: will this work?
    case LUnsolved     => VFinLevel.meta(id)

  def vliftterm(k: VFinLevel, l: VFinLevel, a: VTy, x: Val): Val =
    x match
      case VRigid(hd, SPrim(sp, PLower, args)) => VRigid(hd, sp)
      case VFlex(hd, SPrim(sp, PLower, args))  => VFlex(hd, sp)
      case VGlobal(hd, SPrim(sp, PLower, args), v) =>
        VGlobal(hd, sp, () => vliftterm(k, l, a, v()))
      case _ => VLiftTerm(k, l, a, x)

  private def vsing(l: VFinLevel, a: VTy, x: Val): Val = x match
    case VRigid(hd, SPrim(sp, PSingElim, args)) => VRigid(hd, sp)
    case VFlex(hd, SPrim(sp, PSingElim, args))  => VFlex(hd, sp)
    case VGlobal(hd, SPrim(sp, PSingElim, args), v) =>
      VGlobal(hd, sp, () => vsing(l, a, v()))
    case _ => VSingCon(l, a, x)

  private def vpack(
      l: VFinLevel,
      k: VFinLevel,
      a: VTy,
      b: VTy,
      x: Val,
      t: Val
  ): Val = t match
    case VRigid(hd, SPrim(sp, PUnpack, args)) => VRigid(hd, sp)
    case VFlex(hd, SPrim(sp, PUnpack, args))  => VFlex(hd, sp)
    case VGlobal(hd, SPrim(sp, PUnpack, args), v) =>
      VGlobal(hd, sp, () => vpack(l, k, a, b, x, v()))
    case _ => VPack(l, k, a, b, x, t)

  private def vprim(x: PrimName) = x match
    case PLiftTerm =>
      vlamlvl(
        "k",
        k =>
          vlamlvl(
            "l",
            l => vlamI("A", a => vlam("x", x => vliftterm(k, l, a, x)))
          )
      )
    case PLower =>
      vlamlvl(
        "k",
        k =>
          vlamlvl(
            "l",
            l =>
              vlamI(
                "A",
                a =>
                  vlam(
                    "x",
                    x =>
                      vprimelim(
                        PLower,
                        List(Left(k), Left(l), Right((a, Impl(Unif)))),
                        x
                      )
                  )
              )
          )
      )
    case PSingCon =>
      vlamlvl("l", l => vlamI("A", a => vlam("x", x => vsing(l, a, x))))
    case PSingElim =>
      vlamlvl(
        "l",
        l =>
          vlamI(
            "A",
            a =>
              vlamI(
                "x",
                x =>
                  vlam(
                    "s",
                    s =>
                      vprimelim(
                        PSingElim,
                        List(
                          Left(l),
                          Right((a, Impl(Unif))),
                          Right((x, Impl(Unif)))
                        ),
                        s
                      )
                  )
              )
          )
      )
    case PPack =>
      vlamlvl(
        "l",
        l =>
          vlamlvl(
            "k",
            k =>
              vlamI(
                "A",
                a =>
                  vlamI(
                    "B",
                    b =>
                      vlamI("x", x => vlam("t", t => vpack(l, k, a, b, x, t)))
                  )
              )
          )
      )
    case PUnpack =>
      vlamlvl(
        "l",
        l =>
          vlamlvl(
            "k",
            k =>
              vlamI(
                "A",
                a =>
                  vlamI(
                    "B",
                    b =>
                      vlamI(
                        "x",
                        x =>
                          vlam(
                            "n",
                            n =>
                              vprimelim(
                                PUnpack,
                                List(
                                  Left(l),
                                  Left(k),
                                  Right((a, Impl(Unif))),
                                  Right((b, Impl(Unif))),
                                  Right((x, Impl(Unif)))
                                ),
                                n
                              )
                          )
                      )
                  )
              )
          )
      )
    case PElimId =>
      vlamlvl(
        "k",
        k =>
          vlamlvl(
            "l",
            l =>
              vlamI(
                "A",
                a =>
                  vlamI(
                    "x",
                    x =>
                      vlam(
                        "P",
                        p =>
                          vlam(
                            "refl",
                            refl =>
                              vlamI(
                                "y",
                                y =>
                                  vlam(
                                    "p",
                                    pp =>
                                      vprimelim(
                                        PElimId,
                                        List(
                                          Left(k),
                                          Left(l),
                                          Right((a, Impl(Unif))),
                                          Right((x, Impl(Unif))),
                                          Right((p, Expl)),
                                          Right((refl, Expl)),
                                          Right((y, Impl(Unif)))
                                        ),
                                        pp
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          )
      )
    case PElimEnum =>
      vlamlvl(
        "k",
        k =>
          vlam(
            "P",
            p =>
              vlam(
                "nil",
                nil =>
                  vlam(
                    "cons",
                    cons =>
                      vlam(
                        "e",
                        e =>
                          vprimelim(
                            PElimEnum,
                            List(
                              Left(k),
                              Right((p, Expl)),
                              Right((nil, Expl)),
                              Right((cons, Expl))
                            ),
                            e
                          )
                      )
                  )
              )
          )
      )
    case PElimTag =>
      vlamlvl(
        "k",
        k =>
          vlam(
            "P",
            p =>
              vlam(
                "z",
                z =>
                  vlam(
                    "s",
                    s =>
                      vlamI(
                        "e",
                        e =>
                          vlam(
                            "t",
                            t =>
                              vprimelim(
                                PElimTag,
                                List(
                                  Left(k),
                                  Right((p, Expl)),
                                  Right((z, Expl)),
                                  Right((s, Expl)),
                                  Right((e, Impl(Unif)))
                                ),
                                t
                              )
                          )
                      )
                  )
              )
          )
      )
    case _ => VPrim(x)

  def vappPruning(v: Val, pr: Pruning)(implicit env: Env): Val =
    (env, pr) match
      case (EEmpty, Nil)                 => v
      case (EVal(env, t), Some(i) :: pr) => vapp(vappPruning(v, pr)(env), t, i)
      case (ELevel(env, t), Some(_) :: pr) => vapp(vappPruning(v, pr)(env), t)
      case (EVal(env, _), None :: pr)      => vappPruning(v, pr)(env)
      case (ELevel(env, _), None :: pr)    => vappPruning(v, pr)(env)
      case _                               => impossible()

  def vlinsertedmetaspine(sp: List[Boolean])(implicit
      env: Env
  ): List[VFinLevel] =
    (env, sp) match
      case (EEmpty, Nil)                 => Nil
      case (ELevel(env, t), true :: sp)  => t :: vlinsertedmetaspine(sp)(env)
      case (ELevel(env, t), false :: sp) => vlinsertedmetaspine(sp)(env)
      case (EVal(env, t), false :: sp)   => vlinsertedmetaspine(sp)(env)
      case _                             => impossible()

  def vlspine(sp: List[Boolean])(implicit env: Env): Env =
    (env, sp) match
      case (EEmpty, Nil)                 => EEmpty
      case (ELevel(env, t), true :: sp)  => ELevel(vlspine(sp)(env), t)
      case (ELevel(env, t), false :: sp) => vlspine(sp)(env)
      case (EVal(env, t), false :: sp)   => vlspine(sp)(env)
      case _                             => impossible()

  def eval(l: FinLevel)(implicit env: Env): VFinLevel = l match
    case LVar(ix)   => env(ix).swap.toOption.get
    case LZ         => VFinLevel.unit
    case LS(a)      => eval(a) + 1
    case LMax(a, b) => eval(a) max eval(b)
    case LMeta(id)  => vlmeta(id)
    case LInsertedMeta(id, sp) =>
      getLMeta(id) match
        case LUnsolved => VFinLevelMeta(id, 0, vlinsertedmetaspine(sp))
        case LSolved(dom, v) =>
          try eval(quote(v)(dom))(vlspine(sp))
          catch
            case e =>
              println(s"===$env $sp===")
              throw e

  def eval(l: Level)(implicit env: Env): VLevel = l match
    case LOmega       => VOmega
    case LOmega1      => VOmega1
    case LFinLevel(l) => VFL(eval(l))

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Type(l) => VType(eval(l))
    case Var(ix) => env(ix).toOption.get
    case Prim(x) => vprim(x)
    case Global(uri) =>
      getGlobal(uri) match
        case None => impossible()
        case Some(e) =>
          val value = e.value
          VGlobal(uri, SId, () => value)
    case LabelLit(x) => VLabelLit(x)

    case Let(_, _, v, b) => eval(b)(EVal(env, eval(v)))

    case Lam(x, i, b) => VLam(x, i, Clos(b))
    case App(f, a, i) => vapp(eval(f), eval(a), i)
    case Pi(x, i, t, u1, b, u2) =>
      VPi(x, i, eval(t), eval(u1), Clos(b), eval(u2))

    case LamLvl(x, body)   => VLamLvl(x, CClos(env, body))
    case AppLvl(fn, arg)   => vapp(eval(fn), eval(arg))
    case PiLvl(x, body, u) => VPiLvl(x, CClos(env, body), ClosLvl(env, u))

    case Pair(fst, snd) => VPair(eval(fst), eval(snd))
    case Proj(tm, proj) => vproj(eval(tm), proj)
    case Sigma(x, t, u1, b, u2) =>
      VSigma(x, eval(t), eval(u1), Clos(b), eval(u2))

    case Wk(tm) => eval(tm)(env.tail)

    case Meta(id)           => vmeta(id)
    case AppPruning(tm, pr) => vappPruning(eval(tm), pr)

  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  private def lmetaSpine(sp: List[VFinLevel]): Env = sp match
    case Nil     => EEmpty
    case l :: sp => ELevel(lmetaSpine(sp), l)

  // forcing
  def force(l: VFinLevel): VFinLevel =
    l.metas
      .map { case (id, (n, sp)) =>
        getLMeta(lmetaId(id)) match
          case LUnsolved => VFinLevel.meta(lmetaId(id), sp) + n
          case LSolved(k, v) =>
            val env = lmetaSpine(sp)
            val lv = eval(quote(v)(k))(env)
            force(lv + n)
      }
      .foldRight(VFinLevel(l.k, l.vars))(_ max _)

  def force(v: VLevel): VLevel = v match
    case VFL(l) => VFL(force(l))
    case _      => v

  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _, _) => force(vspine(v, sp))
        case Unsolved(_)     => v
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                       => v

  // quoting
  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SAppLvl(fn, arg) => AppLvl(quote(hd, fn, unfold), quote(arg))
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)
      case SPrim(sp, x, args) =>
        App(
          args.foldLeft(Prim(x))((fn, arg) =>
            arg.fold(
              lv => AppLvl(fn, quote(lv)),
              (a, i) => App(fn, quote(a, unfold), i)
            )
          ),
          quote(hd, sp, unfold),
          Expl
        )

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)
    case HPrim(x) => Prim(x)

  def quote(l: VFinLevel)(implicit k: Lvl): FinLevel =
    val fl = force(l)
    val vars = fl.vars.foldLeft(LZ + fl.k) { case (i, (x, n)) =>
      i max (LVar(mkLvl(x).toIx) + n)
    }
    fl.metas.foldLeft(vars) { case (i, (x, (n, sp))) =>
      i max (LMeta(lmetaId(x)) + n)
    }

  def quote(v: VLevel)(implicit l: Lvl): Level = v match
    case VOmega  => LOmega
    case VOmega1 => LOmega1
    case VFL(l)  => LFinLevel(quote(l))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VType(l)          => Type(quote(l))
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, v) => quote(Global(x), sp, unfold)
      case VLabelLit(x)      => LabelLit(x)

      case VLam(x, i, b) => Lam(x, i, quote(b.inst(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, u1, b, u2) =>
        Pi(
          x,
          i,
          quote(t, unfold),
          quote(u1),
          quote(b.inst(VVar(l)), unfold)(l + 1),
          quote(u2)
        )

      case VLamLvl(x, body) =>
        LamLvl(x, quote(body.inst(VFinLevel.vr(l)), unfold)(l + 1))
      case VPiLvl(x, body, u) =>
        val v = VFinLevel.vr(l)
        PiLvl(x, quote(body.inst(v), unfold)(l + 1), quote(u.inst(v))(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, u1, b, u2) =>
        Sigma(
          x,
          quote(t, unfold),
          quote(u1),
          quote(b.inst(VVar(l)), unfold)(l + 1),
          quote(u2)
        )

  def nf(t: FinLevel)(implicit l: Lvl, env: Env): FinLevel =
    quote(eval(t))

  def nf(t: Level)(implicit l: Lvl, env: Env): Level =
    quote(eval(t))

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = EEmpty): Tm =
    quote(eval(tm), UnfoldAll)
