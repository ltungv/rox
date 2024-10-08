# Rox

`rox` is a feature-complete bytecode virtual machine written in Rust for the Lox programming language. This version performs about 50% worse than the original C-implementation.

## Optimizations

+ [x] Custom fixed-size dynamic array with no bounds check on access.
+ [x] Custom hash table using the interned string pointer. All strings in `rox` are interned upon creation, giving us two benefits:
    + Strings don't need to be hashed in our custom hash table.
    + Strings can be compared by simply comparing the pointers.

## Implemented challenges

+ [x] Do in-place updates on the stack for operators that pop a value and push back a value immediately after.
+ [x] Check arity when calling native functions.
+ [x] Efficient storage for string constants and literals. String objects are interned and stored in a global interner.
+ [x] Memory efficient encoding for line information. Line information is run-length encoded.
+ [ ] Fast dynamic VM' stack.
+ [ ] Support `OP_CONSTANT_LONG`, which takes a 24-bit number to extend the number of constants that can be contained.
+ [ ] String interpolation.
  ```ruby
  var drink = "Tea";
  var steep = 4;
  var cool = 2;
  print "${drink} will be ready in ${steep + cool} minutes.";
  ```
+ [ ] Reuse variable name constant each time a variable is referenced.
+ [ ] Find a better data structure for storing global variables.
+ [ ] Allow more than 256 local variables.
+ [ ] Const declaration.
+ [ ] Better data structure/algorithm for resolving variables at compile time.
+ [ ] Multi-way `switch` statement. Each case automatically jumps to the end of the switch statement after its statements are executed, with no `break` or `fall_through`. Grammar:
  ```
  switchStmt     → "switch" "(" expression ")"
                   "{" switchCase* defaultCase? "}" ;
  switchCase     → "case" expression ":" statement* ;
  defaultCase    → "default" ":" statement* ;
  ```
  1. Evaluate the switch value.
  2. Walk the cases:
    + Evaluate the expression of each case.
    + If the evaluated value equals the switch value, execute the statements under the case, then exit the `switch` statement.
    + If no case matches and there is a default case, execute its statements.
+ [ ] `continue`/`break` statements in a loop.

## Tests and benchmarks

The runners for tests and benchmarks were ported from Dart to avoid installing Dart's SDK. Because Dart 2 has been deprecated, it's a hassle to get everything working. First, ensure the `craftinginterpreters` submodule is pulled to your local machine to get all the official tests and benchmarks.

```sh
git submodule update --init --recursive
```

To test the interpreter, use the command `cargo run --bin test` and give it the path to the test folder and the interpreter binary. You can also build the binary if needed.

```sh
Usage: test --directory <DIRECTORY> --executable <EXECUTABLE>

Options:
  -d, --directory <DIRECTORY>
  -e, --executable <EXECUTABLE>
  -h, --help                     Print help
```

To benchmark and compare different interpreters, use the command `cargo run --bin compare` and give it the path to the benchmark folder and all the interpreter binaries. You can also build the binary if needed.

```sh
Usage: compare [OPTIONS] --directory <DIRECTORY>

Options:
  -d, --directory <DIRECTORY>
  -e, --executables <EXECUTABLES>
  -h, --help                       Print help
```
