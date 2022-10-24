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
  - [x] Postponed checks
  - [ ] Postponed unification
- [ ] Local gluing
  - [ ] Local gluing
  - [ ] Reuse introduced variables in `open` and `export`
  - [ ] Zonking
- [ ] Primitives
  - [x] Primitive constructors
  - [x] Primitive eliminators
  - [x] Unit
  - [x] Void
  - [x] Bool
  - [x] Id
  - [x] Fix
  - [ ] Inductive-recursive fix
  - [ ] Number
  - [ ] String
- [ ] Core verification
  - [ ] Ensure lambda, pair, export and modules are wrapped with a let with type
  - [ ] Core verification
- [ ] Keep track of inserted terms
- [ ] Erasure annotations
- [ ] Instance parameters
- [ ] Compile to ChezScheme
- [ ] Operator sectioning
