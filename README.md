# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

## Desired features

- Type-in-type
- Pi and sigma types
- Fixpoint supporting indexed inductive-recursive types
- Run-time and compile-time irrelevance annotations

## TODO

- [x] Pretty print elaborated terms
- [x] Fix Pi printer
- [x] Fix Pi parser
- [x] Definitions
- [x] Glued evaluation
- [x] Meta variables and solving
- [x] Def with parameters and type annotation
- [x] Let with parameters and type annotation
- [ ] Lambda with type annotation
- [ ] Zonking
- [ ] Implicit function types
- [ ] Sigma types
- [ ] Add a package name
- [ ] Clean up error handling and output
- [ ] Better name generation
- [ ] Investigate laziness
- [ ] Approximate solving for globals
- [ ] Core language verification
