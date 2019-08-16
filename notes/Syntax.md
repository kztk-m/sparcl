Note on Syntax
==============

NB: The language is not indentation sensitive, as being indentation
sensitive complicates parsing process and makes parser definitions tricky.


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

    
## Discussions 

### Brackets for `rev`

It is sometimes tedious to put `rev` to all constructors. Thus, we need more easier notations. 

#### 1. Automatic Promotion 

There are some places we can only put lifted constructors; arguments of other lifted constructors and right-hand sides of invertible cases. 
With the automatic promotion rules, one can simply write

    rev Cons Z (Cons (S Z) Nil) 
    
for 

    rev Cons (rev Z) (rev Cons (rev S (rev Z)) (rev Nil))
    
This approach also removes the syntactic gap between `rev`s used in expressions and patterns. 

A solution is to use the notation of a syntactic context in which constructors are automatically lifted. For example, writing 

    (| Cons Z (Cons (S Z) Nil) |) 
    
to obtain the same effect as above. Using the parentheses `(|` `|)` would not be appropriate as they have a special meaning in the context. How above the following for example? 

    (% Cons Z (Cons (S Z) Nil) %)
    
We can use the syntax also in patterns 

    f (% Nil %)      = (% Nil %)
    f (% Cons a x %) = (% Cons a (f x) %)
        
We might be able to apply inference system to determine whether a constructor
should be lifted or not, but this would introduce confusion; the semantics of normal and lifted constructors are different. 

#### 2. Quotes and Unquotes

Since the language is a two-level system, we may be able to borrow quotes and unquote syntax.    


### Keyword `rev`

The keyword `rev` is too lengthy. More shorter form would be nicer. For example:

  - `` `Cons``
  - `+Cons` 
  - `*Cons`
  - `%Cons` 
  - `$Cons` 
  - `&Cons` 
  - `Cons%`
  - `Cons$`
  - `Cons&`
  - `Cons#`
  - `Cons*` 

I personally like prefixing `%`. Another choice is to use the unicode superscript `ʳ` as a postfix as `Consʳ`. 

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




