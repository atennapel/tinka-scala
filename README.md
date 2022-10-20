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
- [x] Pretty printing
- [ ] Global gluing and importing
  - [x] Basic loading
  - [x] Forcing/unfold modes
  - [x] Open syntax
  - [x] Renaming
  - [x] Toposort imports
  - [x] Load from URI generally (http/file schemes)
  - [x] Open with hiding
  - [x] Syntax exporting
  - [ ] Signatures
  - [ ] Modules
- [ ] Elaboration with metas
  - [x] Implicit functions
  - [x] Meta variables
  - [x] Unification with pruning
  - [x] Insert metas in elaboration
  - [x] Postponed named holes
  - [ ] Zonking
- [ ] Local gluing
  - [ ] Local gluing
  - [ ] Reuse introduced variables in `open` and `export`
- [ ] Primitives
  - [x] Unit
  - [ ] Void
  - [ ] Bool
  - [ ] Id
  - [ ] Fix
  - [ ] Number
  - [ ] String
- [ ] Core verification
  - [ ] Ensure lambda, pair and export are wrapped with a let with type
  - [ ] Core verification
- [ ] Keep track of inserted terms
- [ ] Erasure annotations
- [ ] Instance parameters
- [ ] Compiler
- [ ] Postponing
