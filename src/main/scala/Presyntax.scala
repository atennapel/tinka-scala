import Common.*

object Presyntax:
  enum RArgInfo:
    case RArgNamed(name: Name, impl: ImplMode)
    case RArgIcit(icit: Icit)
  export RArgInfo.*

  enum RProjType:
    case RFst
    case RSnd
    case RNamed(name: Name)

    override def toString: String = this match
      case RFst      => ".1"
      case RSnd      => ".2"
      case RNamed(x) => s".$x"
  export RProjType.*

  enum RLevel:
    case RLVar(name: Name)
    case RLS(lvl: RLevel)
    case RLZ
    case RLMax(a: RLevel, b: RLevel)
    case RLHole
    case RLPos(pos: Pos, lvl: RLevel)

    def isPos: Boolean = this match
      case RLPos(_, _) => true
      case _           => false

    override def toString: String = this match
      case RLVar(x)    => x.toString
      case RLS(l)      => s"(S $l)"
      case RLZ         => s"0"
      case RLMax(a, b) => s"(max $a $b)"
      case RLHole      => s"_"
      case RLPos(_, l) => l.toString

    def freeVars: Set[Name] = this match
      case RLVar(x)    => Set(x)
      case RLS(l)      => l.freeVars
      case RLMax(a, b) => a.freeVars ++ b.freeVars
      case RLPos(_, l) => l.freeVars
      case _           => Set.empty
  export RLevel.*

  enum SigDecl:
    case SLet(name: Name, ty: Option[RTy])
    case SDef(priv: Boolean, name: Name, ty: Option[RTy], value: RTm)
    case SOpen(
        exp: Boolean,
        tm: RTm,
        names: Option[List[(Name, Option[Name])]],
        hiding: List[Name]
    )

    def globals: Set[String] = this match
      case SLet(_, t) => t.map(_.globals).getOrElse(Set.empty)
      case SDef(_, _, t, v) =>
        t.map(_.globals).getOrElse(Set.empty) ++ v.globals
      case SOpen(_, t, _, _) => t.globals

    override def toString: String = this match
      case SLet(name, ty) =>
        ty match
          case Some(ty) => s"$name : $ty"
          case None     => s"$name"
      case SDef(priv, name, ty, value) =>
        ty match
          case Some(ty) =>
            s"${if priv then "private " else ""}$name : $ty = $value"
          case None => s"${if priv then "private " else ""}$name = $value"
      case SOpen(exp, t, None, Nil) =>
        s"${if exp then "export " else ""}open $t"
      case SOpen(exp, t, None, hiding) =>
        s"${if exp then "export " else ""}open $t hiding (${hiding.mkString(", ")})"
      case SOpen(exp, t, Some(ns), Nil) =>
        s"${if exp then "export " else ""}open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")})"
      case SOpen(exp, t, Some(ns), hiding) =>
        s"${if exp then "export " else ""}open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}) hiding (${hiding.mkString(", ")})"
  export SigDecl.*

  enum ModDecl:
    case DLet(priv: Boolean, name: Name, ty: Option[RTy], value: RTm)
    case DOpen(
        exp: Boolean,
        tm: RTm,
        names: Option[List[(Name, Option[Name])]],
        hiding: List[Name]
    )

    def globals: Set[String] = this match
      case DLet(_, _, t, v) =>
        t.map(_.globals).getOrElse(Set.empty) ++ v.globals
      case DOpen(_, t, _, _) => t.globals

    override def toString: String = this match
      case DLet(priv, name, ty, value) =>
        ty match
          case Some(ty) =>
            s"${if priv then "private " else ""}$name : $ty = $value"
          case None => s"${if priv then "private " else ""}$name = $value"
      case DOpen(exp, t, None, Nil) =>
        s"${if exp then "export " else ""}open $t"
      case DOpen(exp, t, None, hiding) =>
        s"${if exp then "export " else ""}open $t hiding (${hiding.mkString(", ")})"
      case DOpen(exp, t, Some(ns), Nil) =>
        s"${if exp then "export " else ""}open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")})"
      case DOpen(exp, t, Some(ns), hiding) =>
        s"${if exp then "export " else ""}open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}) hiding (${hiding.mkString(", ")})"
  export ModDecl.*

  type RTy = RTm
  enum RTm:
    case RType(lvl: RLevel)
    case RVar(name: Name)
    case RGlobal(uri: String)
    case RLabelLit(name: Name)

    case RLet(name: Name, ty: Option[RTy], value: RTm, body: RTm)
    case ROpen(
        tm: RTm,
        names: Option[List[(Name, Option[Name])]],
        hiding: List[Name],
        body: RTm
    )
    case RExport(
        names: Option[List[(Name, Option[Name])]],
        hiding: List[Name]
    )
    case RSig(
        params: List[(Bind, Option[(Icit, Option[RTy])])],
        decls: List[SigDecl]
    )
    case RMod(
        params: List[(Bind, Option[(Icit, Option[RTy])])],
        decls: List[ModDecl]
    )

    case RLam(bind: Bind, info: RArgInfo, ty: Option[RTy], body: RTm)
    case RApp(fn: RTm, arg: RTm, info: RArgInfo)
    case RPi(bind: Bind, icit: Icit, ty: RTy, body: RTy)

    case RPiLvl(name: Bind, body: RTy)
    case RAppLvl(fn: RTm, arg: RLevel, info: Option[Name])
    case RLamLvl(bind: Bind, info: Option[Name], body: RTm)

    case RPair(fst: RTm, snd: RTm)
    case RProj(tm: RTm, proj: RProjType)
    case RSigma(bind: Bind, ty: RTy, body: RTy)

    case RPos(pos: Pos, tm: RTm)
    case RHole(name: Option[Name])

    def isPos: Boolean = this match
      case RPos(_, _) => true
      case _          => false

    def globals: Set[String] = this match
      case RGlobal(uri) => Set(uri)
      case RLet(_, t, v, b) =>
        t.map(_.globals).getOrElse(Set.empty) ++ v.globals ++ b.globals
      case ROpen(tm, _, _, b) => tm.globals ++ b.globals
      case RMod(ps, ds) =>
        val psg = ps.foldRight[Set[String]](Set.empty[String]) {
          case ((_, None), s) => s
          case ((_, Some((_, oty))), s) =>
            s ++ oty.map(_.globals).getOrElse(Set.empty)
        }
        val dsg = ds.foldRight[Set[String]](Set.empty) { case (d, s) =>
          s ++ d.globals
        }
        psg ++ dsg
      case RSig(ps, ds) =>
        val psg = ps.foldRight[Set[String]](Set.empty[String]) {
          case ((_, None), s) => s
          case ((_, Some((_, oty))), s) =>
            s ++ oty.map(_.globals).getOrElse(Set.empty)
        }
        val dsg = ds.foldRight[Set[String]](Set.empty) { case (d, s) =>
          s ++ d.globals
        }
        psg ++ dsg
      case RLam(_, _, t, b) =>
        t.map(_.globals).getOrElse(Set.empty) ++ b.globals
      case RApp(fn, arg, _) => fn.globals ++ arg.globals
      case RPi(_, _, t, b)  => t.globals ++ b.globals
      case RPair(fst, snd)  => fst.globals ++ snd.globals
      case RProj(t, _)      => t.globals
      case RSigma(_, t, b)  => t.globals ++ b.globals
      case RPos(_, t)       => t.globals
      case RPiLvl(_, b)     => b.globals
      case RAppLvl(a, _, _) => a.globals
      case RLamLvl(_, _, b) => b.globals
      case _                => Set.empty

    override def toString: String = this match
      case RType(RLZ)             => "Type"
      case RType(lvl)             => s"Type $lvl"
      case RLabelLit(x)           => s"'$x"
      case RVar(Name("()"))       => "()"
      case RVar(Name("[]"))       => "[]"
      case RVar(x)                => s"$x"
      case RGlobal(x)             => s"#$x"
      case RLet(x, Some(t), v, b) => s"(let $x : $t = $v; $b)"
      case RLet(x, None, v, b)    => s"(let $x = $v; $b)"
      case RSig(ps, ds) =>
        val pss: List[String] = ps.map {
          case (x, None)                         => s"<$x>"
          case (x, Some((Expl, None)))           => s"$x"
          case (x, Some((Expl, Some(ty))))       => s"($x : $ty)"
          case (x, Some((Impl(Unif), None)))     => s"{$x}"
          case (x, Some((Impl(Unif), Some(ty)))) => s"{$x : $ty}"
          case (x, Some((Impl(Inst), None)))     => s"{{$x}}"
          case (x, Some((Impl(Inst), Some(ty)))) => s"{{$x : $ty}}"
        }
        s"(sig${if pss.isEmpty then "" else s" ${pss.mkString(" ")}"} { ${ds.mkString("; ")} })"
      case RMod(ps, ds) =>
        val pss: List[String] = ps.map {
          case (x, None)                         => s"<$x>"
          case (x, Some((Expl, None)))           => s"$x"
          case (x, Some((Expl, Some(ty))))       => s"($x : $ty)"
          case (x, Some((Impl(Unif), None)))     => s"{$x}"
          case (x, Some((Impl(Unif), Some(ty)))) => s"{$x : $ty}"
          case (x, Some((Impl(Inst), None)))     => s"{{$x}}"
          case (x, Some((Impl(Inst), Some(ty)))) => s"{{$x : $ty}}"
        }
        s"(mod${if pss.isEmpty then "" else s" ${pss.mkString(" ")}"} { ${ds.mkString("; ")} })"
      case ROpen(t, None, Nil, b) => s"(open $t; $b)"
      case ROpen(t, None, hiding, b) =>
        s"(open $t hiding (${hiding.mkString(", ")}); $b)"
      case ROpen(t, Some(ns), Nil, b) =>
        s"(open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}); $b)"
      case ROpen(t, Some(ns), hiding, b) =>
        s"(open $t (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}) hiding (${hiding.mkString(", ")}); $b)"
      case RExport(None, Nil)    => s"export"
      case RExport(None, hiding) => s"export hiding (${hiding.mkString(", ")})"
      case RExport(Some(ns), Nil) =>
        s"(export (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}))"
      case RExport(Some(ns), hiding) =>
        s"(export (${ns
            .map((x, oy) => s"$x${oy.map(y => s" = $y").getOrElse("")}")
            .mkString(", ")}) hiding (${hiding.mkString(", ")}))"
      case RLam(x, RArgIcit(Expl), Some(t), b)       => s"(\\($x : $t). $b)"
      case RLam(x, RArgIcit(Expl), None, b)          => s"(\\$x. $b)"
      case RLam(x, RArgIcit(Impl(Unif)), Some(t), b) => s"(\\{$x : $t}. $b)"
      case RLam(x, RArgIcit(Impl(Unif)), None, b)    => s"(\\{$x}. $b)"
      case RLam(x, RArgIcit(Impl(Inst)), Some(t), b) => s"(\\{{$x : $t}}. $b)"
      case RLam(x, RArgIcit(Impl(Inst)), None, b)    => s"(\\{{$x}}. $b)"
      case RLam(x, RArgNamed(y, Unif), Some(t), b) => s"(\\{$x : $t = $y}. $b)"
      case RLam(x, RArgNamed(y, Unif), None, b)    => s"(\\{$x = $y}. $b)"
      case RLam(x, RArgNamed(y, Inst), Some(t), b) =>
        s"(\\{{$x : $t = $y}}. $b)"
      case RLam(x, RArgNamed(y, Inst), None, b) => s"(\\{{$x = $y}}. $b)"
      case RApp(fn, arg, RArgIcit(Expl))        => s"($fn $arg)"
      case RApp(fn, arg, RArgIcit(Impl(Unif)))  => s"($fn {$arg})"
      case RApp(fn, arg, RArgIcit(Impl(Inst)))  => s"($fn {{$arg}})"
      case RApp(fn, arg, RArgNamed(y, Unif))    => s"($fn {$y = $arg})"
      case RApp(fn, arg, RArgNamed(y, Inst))    => s"($fn {{$y = $arg}})"
      case RPi(x, Expl, t, b)                   => s"(($x : $t) -> $b)"
      case RPi(x, Impl(Unif), t, b)             => s"({$x : $t} -> $b)"
      case RPi(x, Impl(Inst), t, b)             => s"({{$x : $t}} -> $b)"
      case RPiLvl(x, b)                         => s"(<$x> -> $b)"
      case RLamLvl(x, None, b)                  => s"(\\<$x>. $b)"
      case RLamLvl(x, Some(y), b)               => s"(\\<$x = $y>. $b)"
      case RAppLvl(l, r, None)                  => s"($l <$r>)"
      case RAppLvl(l, r, Some(x))               => s"($l <$x = $r>)"
      case RPair(fst, snd)                      => s"($fst, $snd)"
      case RProj(tm, proj)                      => s"$tm$proj"
      case RSigma(x, t, b)                      => s"(($x : $t) ** $b)"
      case RPos(_, tm)                          => tm.toString
      case RHole(x)                             => s"_${x.getOrElse("")}"
  export RTm.*
