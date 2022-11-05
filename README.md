# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out:

```
sbt "run examples/nat.tinka"
```

## TODO
- [x] Elaboration
- [ ] Unification with pruning
- [ ] Primitives
  - [ ] Universe lifting operators
  - [ ] Unit
  - [ ] Void
  - [ ] Bool
  - [ ] Id
  - [ ] Descriptions
- [ ] Globals
- [ ] Local gluing
- [ ] Importing
