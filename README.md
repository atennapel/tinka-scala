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
- [ ] Global gluing and basic importing
  - [x] Basic loading
  - [x] Forcing/unfold modes
  - [ ] open/import syntax
  - [ ] Load from URI generally
- [ ] Local gluing
- [ ] Meta variables
- [ ] Unification with pruning
- [ ] Elaboration with metas
- [ ] Add Void, Bool primitives
- [ ] Add Identity primitive
- [ ] Add fixpoint primitive
- [ ] Add number primitives
- [ ] Add String primitive
- [ ] Rigid variables
