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
- [ ] Metas
  - [x] Implicit functions and application
  - [x] Basic metas
  - [x] Pruning
  - [x] First-class polymorphism
  - [ ] Try unification postponing
  - [ ] Zonk or let-def metas
- [ ] Pretty printing
- [ ] Source positions in errors
- [ ] Universes
- [ ] Definitions
- [ ] Imports
