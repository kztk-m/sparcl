Note on Syntax
==============

NB: The language is not indentation sensitive, as being indentation
sensitive complicates parsing process and makes parser definitions tricky.


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

## Elaboration of Patterns 

As Haskell, the language supports Haskell-like patterns. 

```
def f P11 P12 ... P1n = ...
    | P21 P22 ... P2n = ...
    ...
    | Pm1 Pm2 ... Pmn = ...
```

Suppose that `Pij = Ckj[~(rev pij)]` where `k` may be common for consecutive `i`s (here, we used `~` for the vector notation). Then, the above code is desugared to:

```
def f x1 x2 ... xn = case (x1,...,xn) of 
   ...
   (Ck1[~xk1], Ck2[~xk2], ..., Ckn[~xkn]) -> 
     case rev (~xk1, ~xk2, ..., ~xkn) of 
       ...
       rev (~pi1, ~pi2, ..., ~pin) -> ei with ... 
       -- for each i that corresponds to k.            
```

This means that `ei` must come up with `with` clause if one of `Pij` contains `rev`.

## Syntactic Sugar for `pin`

The `pin` operator is typically used in the form of:

```
case pin ea (\a -> ...) of 
 rev (a, b) -> ...
```

We propose a syntax 

```
revdo x1 <- e1;
      x2 <- e2;
      ...;
      xn <- en 
in    e          
```

which will be desugared into

```
case pin e1 (\x1 -> 
       pin e2 (\x2 -> 
         ... 
           pin e{n-1} (\x{n-1} -> en)) ...) of 
 rev (x1, (x2, ..., (x{n-1},xn)) ...) -> e  
```


### Tentative Syntax 

Since the role of deferred binding is similar to "<-" in `do` in Haskell, we will borrow the syntax to write

## [Proposal] Brackets for `rev`

It is sometimes tedious to put `rev` to all constructors. Thus, we need more easier notations. 

### 1. Automatic Promotion 

There are some places we can only put lifted constructors; arguments of other lifted constructors and right-hand sides of invertible cases. 
With the automatic promotion rules, one can simply write

    rev Cons Z (Cons (S Z) Nil) 
    
for 

    rev Cons (rev Z) (rev Cons (rev S (rev Z)) (rev Nil))
    
We may be able to apply inference system to determine whether a constructor
should be lifted or not, but this would introduce confusion; the semantics of normal and lifted constructors are different. 

### 2. Quotes and Unquotes

Since the language is a two-level system, we may be able to borrow quotes and unquote syntax.    
    
    

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




