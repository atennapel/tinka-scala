# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out using:

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
  - [ ] Meta context
  - [ ] Meta solving
  - [ ] Meta insertion
- [ ] Pretty printing
- [ ] Universes
