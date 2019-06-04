Syntactic Sugars
================

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

## Desugaring of Patterns in Rules

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

## [Planned] Syntactic Sugar for `pin`

The `pin` operator is typically used in the form of:

```
let R (a, b) = pin ea (\a -> ...)  
in ... 
```

We propose a syntax 

```
let defer x1 = e1
          x2 = e2
          ...
          xn = en 
in e          
```

which will be desugared into

```
let R (x1, (x2, ..., (x{n-1},xn)) ...) =
   pin e1 (\x1 -> 
    pin e2 (\x2 -> 
     ... 
     pin e{n-1} (\x{n-1} -> en
    ))
in e 
```

But, this incompatible with the current syntax. 

```
let def f x = ... g ...
    def g y = ... f ...
in e 
```


### Tentative Syntax 

Since the role of deferred binding is similar to "<-" in `do` in Haskell, we will borrow the syntax to write

```
revdo p1 <- e1; 
      p2 <- e2; 
      ...
      pn <- en;
      before e 
```

which will be desugarred into 

```
let rev (p1, (p2, ..., (p{n-1},pn)) ...) =
   pin e1 (\p1 -> 
    pin e2 (\p2 -> 
     ... 
     pin e{n-1} (\p{n-1} -> en
    ))
in e 
```



## Undetermined Syntax

Should we use `;` instead of `|` for `case`? 

```
case e of 
 p1 -> e1 ;
 p2 -> e2 ; 
 ... ;
 pn -> en 
end
```

Also, should we use `;` instead of `|` for function definitions. 

```
def f p11 p12 ... p1n = e1 ;
      p21 p22 ... p2n = e2 ; 
      ... ; 
      pm1 rm2 ... pmn = em 
```




