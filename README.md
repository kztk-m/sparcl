Sparcl: A Language for Partially-Invertible Computation
=======================================================

Important Difference from the Paper
-----------------------------------

* The concrete syntax is different (in particular, this implementation
  uses a non-indentation-sensitive syntax).
* Since rational numbers are not supported yet, 
  we have not implemented the arithmetic coding


How to Use
----------

First, we need to build the system. We are using [`stack`](https://docs.haskellstack.org/en/stable/README/) for building, so please install `stack` by following the instruction found in the link.

    $ stack build
    
The command may take time as it build all required packages including a version of GHC requested in the build script. 

Then, we can run REPL by:

    $ stack exec sparcl-exe
    
Then, the system shows the following prompt. 

    Sparcl> 

This is the interactive environment; one thing users can do is to type an expression to examine its evaluation results. 

    Sparcl> 1 + 2 
    3 

Also, users can ask the inferred type of an expression. 

    Sparcl> :type \x -> x 
    ...
    forall a b. b # a -> b 
    

We have some examples under `./Examples` in this distribution. Seeing `./Examples/T1.sparcl` would be useful for knowing the syntax of sparcl. The loading can be done by command `:load`.

    Sparcl> :load Examples/T1.sparcl 
    ...
    
Then, you can use types and functions defined in the file. 

    Sparcl> fwd (add (S Z)) (S (S Z))
    ...
    S (S (S Z))
    

Typing `:h` and then enter will show the following help.

    Sparcl> :h
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


Known Issues
------------

* The desugaring of Haskell-like rules do not work correctly, due to
  depth-first renaming of variables. Thus, please use `case` explicitly 
  if one wants to mix rev and non-rev patterns. 
* The system supports importing other modules but this functionality is not tested yet.
