Sparcl: A Language for Partially-Invertible Computation
=======================================================

This is an implementation of a system presented in the following paper.

    Kazutaka Matsuda and Meng Wang: Sparcl: A Language for Partially-Invertible Computation, ICFP 2020. 
    

How to Use
----------

First, install [`ghcup`](https://www.haskell.org/ghcup/) following the instruction found in the link. Then, install `ghc` and `cabal` via `ghcup` by:

    ghcup install cabal 
    ghcup install ghc 9.6.7

Once this has been done, then type as below to build the system.

    cabal build
    
The command may take some time as it builds all required packages.

Then, we can start the read-eval-print loop by:

    cabal run
    
After invoking the executable, one will see that the system shows the following prompt.

    Sparcl> 

One thing users can do is to input an expression to examine its evaluation results.

    Sparcl> 1 + 2 
    3 

Also, users can ask the inferred type of an expression.

    Sparcl> :type \x -> x 
    ...
    forall a b. b # a -> b 

We have some examples under `./Examples` in this distribution. Seeing `./Examples/T1.sparcl` would be useful for knowing the syntax of Sparcl. The loading can be done by the command `:load`.

    Sparcl> :load Examples/T1.sparcl 
    ...
    
Then, you can use types and functions defined in the file.

    Sparcl> fwd (add (S Z)) (S (S Z))
    ...
    S (S (S Z))
    Sparcl> bwd (add (S Z)) (S (S (S Z)))
    ...
    S (S Z)
    

Typing `:help` and then enter will show the help as below.

    Sparcl> :help
    :quit
        Quit REPL.
    :load FILEPATH
        Load a program.
    :reload
        Reload the last program.
    :help
        Show this help.
    :type EXP
        Print the expression's type.

Currently, there is no batch execution mode. Invoking the executable with a file name is equivalent to invoking it without a file name and executing command `:load`.

Synopses of `Examples`
----------------------

There are roughly two sorts of examples, focusing on linear typing and partial invertibility respectively.

### Examples concerning Linear Typing

* `App.sparcl`, `App0.sparcl`, `App1.sparcl`, `App10.sparcl`:
Nested applications of the function application function.
* `F.sparcl`:
Some higher-order functions extracted from Haskell's `Prelude`.
* `GV_func.sparcl`:
An example taken from the papers J. Garret Morris: The Best of Both Worlds Linear Functional Programming without Compromise, ICFP 2016, and Sam Lindley: Embedding Session Types in Haskell, Haskell 2016.
* `T2.sparcl`, `T3.sparcl`, `T4.sparcl`, `T5.sparcl`:
Miscellaneous examples, mainly used for debugging purpose.

`App*.sparcl`, `F.sparcl` and `GV_func.sparcl` are used in the experiments in Kazutaka Matsuda: "Modular Inference of Linear Types for Multiplicity-Annotated Arrows". ESOP 2020.

### Examples concerning Partially Invertible Computation

In the following, section numbers refer to those in the paper.

* `Fib.sparcl`: An invertible function that computes a consecutive fibonacci numbers from an index.
* `S2l.sparcl`: An invertible function that computes differences of two consecutive elements in a list (Sections 1 and 2)
* `Pi.sparcl`: An invertible function that computes pre- and in-order traversals (Section 4.1)
* `Huff.sparcl`: An invertible version of Huffman coding (Section 4.2)
* `Loop.sparcl`: An implementation of the trace operator (mentioned in Section 3.6.4).
* `ArithmeticCoding.sparcl`: An invertible implementation of arithmetic coding.
* `Reverse.sparcl`: Invertible definitions of the list reversal function.
* `T1.sparcl`: Miscellaneous examples (including `add` and `mul` discussed in Section 2).
* `IllTyped1.sparcl`: A non-example that should be rejected by Sparcl's type checker.

Notable Differences from the Paper (ICFP 2020)
---------------------------------------------

* The concrete syntax is different (in particular, this implementation
  uses a non-indentation-sensitive syntax, and the keyword `rev` is used instead of non-ascii bullets to mark invertible types)
* The interpreter uses value environments (as usual) instead of substitutions. HOAS-like representations are adopted for values; particularly, function values are represented by `Value -> Eval Value` where `Eval` is a monad used for the (unidirectional) evaluation. This applies also to residuals, which are represented by pairs of functions implementing the forward and backward evaluations.
* The forward evaluation ignores linearity.
* The `Eval` monad mentioned above is used for providing fresh names of invertible variables, which essentially implements alpha renaming mentioned in Fig. 3.

Rough Explanation of Syntax
--------------------------

Here, we briefly explain the syntax of Sparcl. This explanation is not a complete documentation, but only to help understand the examples.

A program consists of type or function definitions. A type declaration can be datatype declarations, or type synonym declarations.

    data T a1 ... an = C Ty1 ... Tym | ... | C' Ty1' ... Tyk
    type T a1 ... an = T Ty1 ... Tym
    
Their syntax is a similar to Haskell's one.
Unlike Haskell, there is no partial applications of types and each type variable must range over types or multiplicities.
Currently, the system does not have kind-checking.
So, it may accept some ill-formed type declarations.

We also allow GADTs, but use a different syntax from Haskell's. See, `GV_func.sparcl` for an example.

Types in Sparcl include following ones.

* primitive types (such as `Int`, `Char` and `Bool`)
* type constructor applications (such as `List Int`)
* multiplicity-annotated function types (such as `Int # Omega -> Bool`)
* tuple types (such as `(Int, Bool)`)
* polymorphic types (with constraints) (such as `forall a p. a # p -> a` and `forall a b p q r. p <= q => (a # p -> b) # r -> a # q -> b`)
* invertible types (such as `rev Int` and `rev (List Int)`)

Sparcl's type system is rank 1 and polymorphic types can appear in limited positions,
namely outermost positions of signature declarations (i.e., `Ty` of `sig f : Ty` below).

A function definition has the form of:

    sig f : Ty 
    def f p1 ... pn = e1 with e1' 
        | ...
        | q1 ... qn = ek with e2' 
        
Here, the `with` part is required only if patterns of a branch contain an invertible patterns `rev p`. Branches with invertible patterns will be converted to invertible `case`s internally, while there is no such special `case` expression in the surface language.
The `sig` declaration is optional.

Other than invertible patterns `rev p`, patterns can also be:

* variable patterns (such as `x`)
* constructor patterns (such as `Cons a x` and `Nil`)
* tuple patterns (such as `(x,y)` and `()`)

Invertible patterns cannot be nested. Value patterns and guards are not supported yet.

Expressions are rather standard except invertible constructors `rev C`. We can use:

* variable expressions
* constructor expressions (such as `Cons`)
* tuple expressions (such as `(1, 2)`)
* applications (such as `f 1`)
* case expressions (such as `case x of | Nil -> True | Cons _ _ -> False end`)
* non-recursive let-expression (such as `let rev (x, y) <- e1 in e2`)

Notice that `case` expressions require closing delimiters.

Local definitions are supported via `let ... in e` and `where ... end`.  The former is an expression while the latter can only appear after a branch (such as `def f x = y where def y = 1 end` and `case 1 of x -> y where def y = 1 end end`).

Publications
------------

* Kazutaka Matsuda and Meng Wang: "Sparcl: A Language for Partially-Invertible Computation". J. Funct. Program. 34: e4 (2024)
* Kazutaka Matsuda and Meng Wang: "Sparcl: A Language for Partially-Invertible Computation". ICFP 2020: 118:1-118:31
* Kazutaka Matsuda: "Modular Inference of Linear Types for Multiplicity-Annotated Arrows". ESOP 2020: 456-483

Known Issues
------------

* The importing feature is not thoroughly tested yet.
* We are experimenting code generation for integration to other systems such as Haskell/GHC. This functionality is partially implemented and the system places such generated Haskell files under the directory `.sparcl`.
* The primitive operations now have linear function types (such as `(+) : Int -o Int -o Int`), but they may have unrestricted function types (such as `(+) : Int -> Int -> Int`).
* Pretty-printing for tuple values is suboptimal.
