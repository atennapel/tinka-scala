# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out:

```
sbt "run examples/nat.tinka"
```

## TODO
- [x] Elaboration
- [x] Unification with pruning
- [x] Primitives
  - [x] Machinery
  - [x] Universe lifting operators
  - [x] Unit
  - [x] Void
  - [x] Bool
  - [x] Id
- [ ] Globals
- [ ] Importing
- [ ] Local gluing
- [ ] Add subtyping coercion to avoid `isNeutral` in elaboration
- [ ] Inductive types (descriptions)
- [ ] Keep track of inserted terms, hide in output
- [ ] Erasure
- [ ] Compilation
- [ ] REPL
