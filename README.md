Sparcl: A Language for Partially-Invertible Computation
=======================================================


How to Use
----------

First, we need to build the system. We are using [`stack`](https://docs.haskellstack.org/en/stable/README/) for building, so please install `stack` by following the instruction found in the link. Once `stack` has been installed, then type as below to build the system. 

    $ stack build
    
The command may take time as it build all required packages including a version of GHC.

Then, we can start the read-eval-print loop by:

    $ stack exec sparcl-exe
    
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

There are roughly two sorts of examples: ones to check linear typing and the others to check partial invertiblity. 

### Examples concerning Linear Typing

 * `App.sparcl`, `App0.sparcl`, `App1.sparcl`, `App10.sparcl`: 
Nested applications of the function application function.
 * `F.sparcl`:
Some higher-order functions extracted from Haskell's `Prelude`.
 * `GV_func.sparc`:
An example taken from the papers J. Garret Morris: The Best of Both Worlds Linear Functional Programming without Compromise, ICFP 2016, and Sam Lindley: Embedding Session Types in Haskell, Haskell 2016.
 * `T2.sparcl`, `T3.sparcl`, `T4.sparcl`, `T5.sparcl`: 
Miscellaneous examples, mainly used for debugging purpose. 

The first 4 items (`App*.sparcl`, `F.sparcl` and `GV_func.sparcl`) were used in the experiments in our ESOP 2020 paper. 

### Examples concerning Partially Invertible Computation

In the following, section numbers refer to those in our ICFP 2020 paper. 

 * `Fib.sparcl`: An invertible function that computes a consecutive fibonacci numbers from an index. 
 * `S2l.sparcl`: An invertible function that computes differences of two consecutive elements in a list (Sections 1 and 2) 
 * `Pi.sparcl`: An invertible pre- and in-order traversals (Section 4.1)
 * `Huff.sparcl`: An invertible version of Huffman coding (Section 4.2)
 * `Loop.sparcl`: An implementation of the trace operator (mentioned in Section 3.6.4) and some examples using it. 
 * `ArithmeticCoding.sparcl`: an invertible implementation of arithmetic coding. 
 * `Reverse.sparcl`: Some invertible definitions of the list reversal function.
 * `T1.sparcl`: Miscellaneous examples (including `add` and `mul` discussed in Section 2). 
 * `IllTyped1.sparcl`: A non-example that should be rejected by Sparcl's type checker. 

Notable Differences from Our ICFP 2020 Paper
---------------------------------------------

* The concrete syntax is different (in particular, this implementation
  uses a non-indentation-sensitive syntax)
* The interpreter uses value environments (as usual) instead of substitutions. HOAS-like representations are adopted for values; particularly, function values are represented by `Value -> Eval Value` where `Eval` is a monad used for the (unidirectional) evaluation. This applies also to residuals, which are represented by pairs of functions, which implements the forward and backward evaluations. 
* The forward evaluation are not aware of linearity, as separation of environments would have large runtime overhead. 
* The `Eval` monad mentioned above is used for providing fresh names of invertible variables, which essentially implements alpha renaming mentioned in Fig. 3.

Publications
------------

 * Kazutaka Matsuda and Meng Wang: "Sparcl: A Language for Partially-Invertible Computation". to appear in ICFP 2020. 
 * Kazutaka Matsuda: "Modular Inference of Linear Types for Multiplicity-Annotated Arrows". ESOP 2020: 456-483


Known Issues
------------

* The system supports importing other modules but this functionality is not tested yet.
* We are experimenting code generation for integration to other systems such as Haskell/GHC. This functionality is partially implemented and the system places such generated Haskell files under the directory `.sparcl`. 
