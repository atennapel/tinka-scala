# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out:

```
sbt "run examples/nat.tinka"
```

## TODO
- [x] Basic language
- [x] Parser
- [x] Sigmas
- [x] Implicit functions
- [x] Pretty printing
- [x] Add unit primitive
- [ ] Fix name shadowing issue in pretty printing
- [ ] Global gluing and basic importing
- [ ] Local gluing
- [ ] Meta variables
- [ ] Unification with pruning
- [ ] Elaboration with metas
- [ ] Add Void, Bool primitives
- [ ] Add Identity primitive
- [ ] Add fixpoint primitive
- [ ] Add number primitives
- [ ] Add String primitive
