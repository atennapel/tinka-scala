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
- [x] Subtyping coercions
  - [x] Add subtyping coercion to avoid `isNeutral` in elaboration
  - [x] Subtyping along pi types
  - [x] Subtyping along sigma types
  - [x] Subtyping along level pi types
- [x] Globals
- [ ] Importing and exporting
  - [x] open
  - [x] export
  - [ ] Signatures
  - [ ] Modules
- [ ] Local gluing
- [ ] Inductive types (descriptions)
- [ ] Keep track of inserted terms, hide in output
- [ ] Erasure
- [ ] REPL
- [ ] Core verification
  - [ ] Ensure lambda, pair, export and modules are wrapped with a let with type
  - [ ] Core verification
- [ ] Instance parameters
- [ ] Compile to ChezScheme
- [ ] Operator sectioning
