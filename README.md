# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out:

```
sbt "run lib/bool.tinka"
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
  - [x] Sing
  - [x] Newtype
- [x] Subtyping coercions
  - [x] Add subtyping coercion to avoid `isNeutral` in elaboration
  - [x] Subtyping along pi types
  - [x] Subtyping along sigma types
  - [x] Subtyping along level pi types
- [x] Globals
- [x] Importing and exporting
  - [x] open
  - [x] export
  - [x] Modules
    - [x] Basic modules
    - [x] Private definitions
    - [x] Module parameters
    - [x] Open in module
    - [x] Open export in module
  - [x] Signatures
    - [x] Basic signatures
    - [x] Signature parameters
    - [x] Private definitions
    - [x] Open in signatures
- [x] Zonking
- [ ] Inductive types (descriptions)
  - [x] Labels
  - [x] Enums
  - [ ] Tags
  - [ ] Descriptions
- [ ] Instance parameters
  - [x] Simple instance search
  - [ ] Recursive instance search
  - [ ] Retry on meta solving
- [ ] Erasure
- [ ] Local gluing
- [ ] Keep track of inserted terms, hide in output
- [ ] REPL
- [ ] Core verification
  - [ ] Ensure lambda, pair, export and modules are wrapped with a let with type
  - [ ] Core verification
- [ ] Compile to ChezScheme
- [ ] Operator sectioning
- [ ] Module extensions
  - [ ] Open export in signatures
  - [ ] Manifest fields
