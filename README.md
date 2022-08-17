# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out implicit:

```
sbt "run examples/church.tinka"
```

## TODO
- [x] Parser
- [x] Scala-style operators
  - [x] Basic operators
  - [x] Precendence and associativity
  - [x] Unary operators
  - [x] "if-then-else" operator
- [x] Unit type
- [x] Sigma types
  - [x] Type
  - [x] Pairs
  - [x] Tuples
  - [x] List syntax
  - [x] Projection
  - [x] Named projection
- [x] Metas
  - [x] Implicit functions and application
  - [x] Basic metas
  - [x] Pruning
  - [x] First-class polymorphism
  - [x] Unification postponing
  - [x] Zonking
- [x] Pretty printing
- [ ] Source positions in errors
- [ ] Universes
- [ ] Definitions
- [ ] Imports
