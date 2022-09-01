# State of the fried-egg project

Any questions? Oliver's internship is over but he is happy to answer questions (oflatt@gmail.com).

Fried egg is an egraph-based optimizer for TAC programs. The kotlin code converts TAC Commands into a an s-expression format that the rust code then parses (`MathOptimization.kt` and `EggTAC.kt`). The rust side uses its axioms to learn equalities in the egraph. Finally, it outputs globally-true equalities that it learned about the program.

Fried egg expects a DSA tac program.
It works by first doing a full SSA of the program so that variables in different blocks have unique names.
It then inserts the SSA program into the egraph, using eclasses instead of variables.
While it runs axioms in the egraph, it unifies variables when it discovers that they are the same across blocks, thus removing extra intermediate variables (see the call to `with_hook`).

The math axioms are generated by our `ruler-evm` project, forked from [Ruler](https://github.com/uwplse/ruler). Ruler figures out math axioms by enumerating things in the egraph and checking if they are true using Z3.
Rules should not be written by hand if possible (instead `ruler-evm` should be extended to generate the needed rules).
See the list of axioms in `ruler-rules.json`.


## Tricks to try

- Different extraction functions with different costs
- Extracting multiple things per eclass
- Extracting one thing per enode in the eclass
- Different time or iter limits to egg
- New rulesets- iter 2 ruleset instead of iter 2 ruleset from ruler-evm?

## To-dos

- It would be great to support all types of TACExpr so that we can really send the whole program to Rust. That would allow us to do cool things like change the structure of blocks/loop optimizations.
- Fix up LogicalEquivalence, which is currently disabled. You need to add a type analysis to the logical_eq stuff so the rules are sound.
- It would be cool to do partial evaluation / automatic inlining in the egraph when we simplify things. Though I'm not sure if it's worth the runtime cost.
Imagine we have a program:
```
Block1: x = 0

Block2: x = 2 * pi

Block3, with parents (Block1 and Block2): y = sin(x)
```
If we try inlining block1 and block2, we find that in both cases y = 0. But we will never find that the x in block1 is equal to the x in block2. (This is just an example, we don't actually support sin or real numbers.)



## Future project: Adapting to perform linear invariant inference

We would like to replace `PointerSimplification.kt` with fried-egg, since it could be much faster and find better simplifications.
The challenge is to not replace assignments that need to maintain a particular shape for other analysis.
In particular, byte array length computations are a problem. There is code that finds these computations in `AllocationAnalysis.kt`, but the PointerSimplification code does it's own ad-hoc thing using the invariants it found.

Besides detecting these cases, it should be a drop-in replacement because we first try to extract linear invariants on the rust side. Make sure to run the `EncoderAnalysisTest.kt` and the `DecoderAnalysisTest.kt`. If those pass the replacement worked.