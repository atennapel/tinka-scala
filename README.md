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
- [x] Source positions in errors
- [x] Universes
  - [x] Level pis
  - [x] Level lambdas
  - [x] Level application
  - [x] Level metas
  - [x] Level unification
- [x] Globals
- [x] Lift, lift and lower
- [ ] Enum
  - [x] Add Enum
  - [x] Add Tag
  - [ ] Eta law for Enum?
  - [ ] Sugar for Enum and Tag
  - [ ] Elaboration rule for Label and Tag
  - [ ] Unit as Tag
- [ ] Imports
- [ ] Hide inserted apps/binders in pretty printing
- [ ] Erasure annotations
- [ ] Reduce source position wrappings
