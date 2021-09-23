# Equality Saturation Based TAC Optimizer 

- Install Rust [here](https://www.rust-lang.org/tools/install)
- Run as follows: `cargo run --release optimize`


# Getting Fried-egg to work with CVT
There's a few things I had to do to get Fried-egg composed with CVT.

## On the rust side
First off, we don't want to spawn sub-processes for each call to Fried-egg because that can be inefficient for larger programs since there will likely be many calls.
So we decided to go with a shared library approach using [UNIFFI](https://mozilla.github.io/uniffi-rs/Overview.html).
It's worth keeping in mind that the simpler the interface you can expose, the easier FFI is.
Here's notes on how to do this.
- First, write your rust code in the `src/lib.rs` file.
- Then make the udl file called `src/tac_optimizer.udl` here.
- Run `uniffi-bindgen scaffolding src/tac_optimizer.udl` to generate the rust side scaffolding code (`src/tac_optimizer.uniffi.rs`).
- Add the line `std::include!("tac_optimizer.uniffi.rs");` at the bottom of the `src/lib.rs` file.
- Run `uniffi-bindgen generate src/tac_optimizer.udl --language kotlin --no-format` to generate the kotlin bindings.
- Finally run `cargo build --release` to generate the shared library (in `target/release/libtac_optimize.dylib`).

This should be sufficient for exposing the rust functionality that you want for the FFI and also for creating the kotlin code.

## On the kotlin / CVT side
Generating the code is just half of the work. Now you also need to make sure you can call the rust functionality from the CVT codebase.
Here's notes on how to do this.
- First copy the `tac_optimizer.kt` file to the right directory (in this case, `main/kotlin/analysis/opt/`) and make sure you import it wherever you are using it.
For example, I was calling code in `tac_optimizer.kt` from `PointerSimplification.kt` and so I included `import uniffi.tac_optimizer.EggAssign` at the top of that file.
- You need to make sure the code is available in the form of a shared library. For this, copy `target/release/libtac_optimize.dylib` under
`src/main/resources`. For some reason, kotlin wants the file to be named as: `libuniffi_tac_optimizer.dylib` so rename it.
- You need edit the `build.gradle.kts` file by adding  `implementation(files("src/main/resources/jna-5.9.0.jar"))` under the `dependencies` which already
has a bunch of similar jar files. NOTE: this is a temporary solution, Make sure you eventually find an online source for `jna` for this so you don't have to manually copy paste this jar in the right directory, update versions, and so on.
- At this point even though `./gradlew assemble` will succeed, IntelliJ will still show red squiggly lines under the jna related imports in `tac_optimizer.kt`. To get rid of those, I right clicked on `src/main` -> `Open Module Settings` -> `Dependencies` -> click on the `+` and add the path to wherever the `jna.jar` is (for example, `src/main/resources/jna-5.9.0.jar` or hopefully online resource).




