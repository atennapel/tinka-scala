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
- [ ] Pretty printing
- [ ] Sigmas
- [ ] Implicit functions
- [ ] Add Void, Unit, Bool primitives
- [ ] Add Identity primitive
- [ ] Meta variables
- [ ] Unification with pruning
- [ ] Elaboration with metas
- [ ] Local and global gluing
- [ ] Add fixpoint primitive
- [ ] Add number primitives
- [ ] Add String primitive
