# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out using:

```
sbt "run lib/sum.tinka"
```

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
- [x] Lambda with type annotation
- [x] Zonking
- [x] Implicit function types
- [x] Add comments
- [x] Debugging flag
- [x] Sigma types
- [x] Add unit type
- [x] Identity type
- [x] Basic importing
- [x] REPL
- [x] Operators
  - [x] Parsing
  - [x] Fix (::) operator
  - [x] Fix prefix operators
- [x] Sigma import expression
- [ ] Erasure annotations
- [ ] Inductive-recursive fixpoint type
- [ ] Add a package name
- [ ] Clean up error handling and output
- [ ] Better name generation
- [ ] Investigate laziness
- [ ] Approximate solving for globals
- [ ] Improve importing
  - [ ] Qualified and selective imports
  - [ ] Import renamings
  - [ ] Toposort imports, check for cycles
  - [ ] Make import statement and expression consistent with each other
- [ ] Core language verification
- [ ] Replace zonking with something more efficient
- [ ] Pruning
- [ ] First-class polymorphism
- [ ] Clean up parser
- [ ] Add explicit Skip in term, to replace shifting
- [ ] Remove Ix and Lvl newtypes
