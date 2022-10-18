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
- [x] Global gluing and importing
  - [x] Basic loading
  - [x] Forcing/unfold modes
  - [x] Open syntax
  - [x] Renaming
  - [x] Toposort imports
- [ ] Elaboration with metas
  - [x] Meta variables
  - [x] Unification with pruning
  - [x] Insert metas in elaboration
  - [ ] Zonking
  - [ ] Postponed named holes
- [ ] Local gluing
  - [ ] Local gluing
  - [ ] Reuse introduced variables in `open`
- [ ] Add Void, Bool primitives
- [ ] Add Identity primitive
- [ ] Add fixpoint primitive
- [ ] Add number primitives
- [ ] Add String primitive
- [ ] Open extensions: hiding
- [ ] Load from URI generally (http/file schemes)
- [ ] Syntax for modules or exporting
