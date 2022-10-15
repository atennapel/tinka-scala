# tinka-scala

Dependently typed programming language implemented in Scala 3.
Typechecking algorithm is based on https://github.com/AndrasKovacs/elaboration-zoo

Try it out implicit:

```
sbt "run examples/church.tinka"
```

## TODO
- [x] Basic language
- [x] Parser
- [x] Sigmas
- [x] Implicit functions
- [ ] Pretty printing
- [ ] Add Identity primitive
- [ ] Local and global gluing
- [ ] Meta variables
- [ ] Unification with pruning
- [ ] Elaboration with metas
- [ ] Add Void, Unit, Bool primitives
- [ ] Add fixpoint primitive
- [ ] Add number primitives
- [ ] Add String primitive
