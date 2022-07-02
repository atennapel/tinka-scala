import Surface.Tm.*

val tm = Let(
  "id",
  Some(Pi("A", Type, Pi("_", Var("A"), Var("A")))),
  Lam("A", Lam("x", Var("x"))),
  Var("id")
)

@main def hello: Unit =
  println(tm)
