# State of the fried-egg project

Any questions? Oliver's internship is over but is happy to answer questions (oflatt@gmail.com).

Fried egg is an egraph-based simplifier for TAC programs. It takes as input a program represented as a series of blocks with assignments to variables in them (see tests in `lin_inv.rs`). It outputs this same format, but tries to simplify each variable's right hand side value.

It works by first inserting the program into the egraph, then running math axioms on the egraph, then extracting the program back out. In an egraph, intermediate variables are bad, so we try to avoid them by keeping a side table of which variables correspond to which eclasses in the egraph.

Initially, each block uses completely independent variables. However, if we learn that a variable is the same for all parents of a block, then we can use it in the child block. See `full_program_2` in `lin_inv.rs` for an example.


## To-dos

- We currently use `logical_equality` for small math simplifications, but we should really just send a small program with one expression in it to `lin_inv` instead and delete that file.
- A big source of bugs is inferring types in `EggTAC.kt` after egg simplifies expressions. Variables are looked up for their type, and then each operator's output type is hard-coded. Constants are inferred to be booleans if they are 0 or 1. Will these always match up between operators and variables?
- Errors from the Rust process tend to disappear in CI, and I'm not sure if they show up from staging. Where are they going? See `RustBlaster.kt` for where we call `redirectError`, which redirects the stderr out to the current process.
- It would be cool to do partial evaluation / automatic inlining in the egraph when we simplify things.
Imagine we have a program:

Block1: x = 0

Block2: x = 2 * pi

Block3, with parents (Block1 and Block2): y = sin(x)

If we try inlining block1 and block2, we find that in both cases y = 0. But we will never find that the x in block1 is equal to the x in block2.




## Future project: Adapting to perform linear invariant inference

We would like to replace `PointerSimplification.kt` with fried-egg, since it could be much faster and find better simplifications.
The challenge is to not replace assignments that need to maintain a particular shape for other analysis.
In particular, byte array length computations are a problem. There is code that finds these computations in `AllocationAnalysis.kt`, but the PointerSimplification code does it's own ad-hoc thing using the invariants it found.

Besides detecting these cases, it should be a drop-in replacement because we first try to extract linear invariants on the rust side. Make sure to run the `EncoderAnalysisTest.kt` and the `DecoderAnalysisTest.kt`. If those pass the replacement worked.