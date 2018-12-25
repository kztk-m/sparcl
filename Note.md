Note
====

Sugared Syntax
--------------

The language is not indentation sensitive, as being indentation
sensitive complicates parsing process and makes it hard-wired to
specific parsers (e.g. happy).


<!--### Keywords

```
sig type data newtype let and in where case of rev with infix infixr infixl 
```

The following words are reserved for future.

```
import module open begin end 
```

### Special Symbols

The following characters cannot be a part of identifiers. 

```
( ) { } , _
```

### Identifiers

Every nonempty combination of letters and symbols are identifiers. Some combinations
like `!` has the special meaning. 
-->

### Desugaring of Patterns in Rules

As Haskell, the language supports Haskell-like patterns. 

```
let f P11 P12 ... P1n = ...
  | f P21 P22 ... P2n = ...
  ...
  | f Pm1 Pm2 ... Pmn = ...
```

Suppose that `Pij = Ckj[~(rev pij)]` where `k` is determined by `i` (here, we used `~` for the vector notation). Then, the above code is desugared to:

```
let f x1 x2 ... xn = case (x1,...,xn) of 
   ...
   (Ck1[~xk1], Ck2[~xk2], ..., Ckn[~xkn]) -> 
     case rev (~xk1, ~xk2, ..., ~xkn) of 
       ...
       rev (~pi1, ~pi2, ..., ~pin) -> ei with ... 
       -- for each i that corresponds to k.            
```

This means that `ei` must come up with `with` clause if one of `Pij` contains `rev`.



