# Language
```
Lift : <k l> -> Type l -> Type (max l k)
lift : <k l> {A : Type l} -> A -> Lift <k> <l> A
lower : <k l> {A : Type k} -> Lift <k> <l> A -> A

lift (lower t) ~> t
lower (lift t) ~> t
```

# Performance
- try out first-order closure
- try out `inline`
- try out making env lazy
- try out making eliminators lazy
- try out making types in values lazy
- try to get rid of `attempt` in parser
- try lazy `Path`
- does overloading have a significant impact?
