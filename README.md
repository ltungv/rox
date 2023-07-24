# Rox

A feature-complete bytecode virtual machine written in Rust for the Lox programming language. This version performs about 50% worse than the original C-implementation.

## Optimizations

+ [x] Caches the chunk instructions pointer. We hold a raw reference into the chunk's list of instructions within our VM struct.
+ [x] Custom fixed-sized stack with no bounds check on access. We hand-roll our own stack implementation that is backed by a fixed-size array.
+ [x] Custom HashMap using the iterned string pointer addresses as its keys. Strings in Lox are hashed upons creation, and the hash value is cached within the string object. Thus, we don't have to recompute hash when accessing the HashMap.

## Implemented challenges

+ [x] Do inplace update on the stack for operators that pop a value and push back a value immediately after.
+ [x] Check arity when calling native functions.
+ [x] Efficient storage for string constants and literals. String objects are interned and stored in a global interner.
+ [x] Memory efficient encoding for line information. Line information is run-length encoded.
+ [ ] Fast dynamic VM' stack.
+ [ ] Support `OP_CONSTANT_LONG` that takes a 24-bit number to extend the number of constants that can be contained.
+ [ ] String interpolation.
  ```ruby
  var drink = "Tea";
  var steep = 4;
  var cool = 2;
  print "${drink} will be ready in ${steep + cool} minutes.";
  ```
+ [ ] Reuse variable name constant each time a variable is referenced.
+ [ ] Find better data structure for storing global variables.
+ [ ] Allow more than 256 local variables.
+ [ ] Const declaration.
+ [ ] Better data structure/algorithm for resoving variable at compile time.
+ [ ] Multi-way `switch` statement. Each case automatically jumps to the end of the switch statement after its statements are done, no `break` or `fallthrough`. Grammar:
  ```
  switchStmt     → "switch" "(" expression ")"
                   "{" switchCase* defaultCase? "}" ;
  switchCase     → "case" expression ":" statement* ;
  defaultCase    → "default" ":" statement* ;
  ```
  1. Evaluate the switch value.
  2. Walk the cases:
    + Evaluate the expression of each case.
    + If the evaluated value equal to the switch value, execute the statements under the case, then exit the `switch` statement.
    + If no case matches and there is a default case, execute its statements.
+ [ ] `continue`/`break` statement in loop.

