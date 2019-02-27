Sparcl: A Language for Partially-Invertible Computation
=======================================================

How to Use
----------

First, we need to build the system.

    $ stack build
    
Then, we can run REPL by:

    $ stack exec sparcl-exe
    
Then, there will be a prompt of the form. 

    Sparcl> 

This is the interactive environment for our system. 

    Sparcl> 1 + 2 
    3 
    
Typing `:h` and the enter will show the following help.

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

We have the following examples under `./examples` in this distribution. 

  * t1.sparcl
  * s2l.sparcl
  * pi.sparcl 
  
Seeing `./examples/t1.sparcl` would be useful for knowing sparcl.


Known Bugs 
----------

* The desugaring of Haskell-like rules do not work correctly, due to
  depth-first renaming of variables. Thus, please use `case` explicitly 
  if one wants to mix rev and non-rev patterns. 
  
