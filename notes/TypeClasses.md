Type Classes in Sparcl
=====================

Author: Claude (Anthropic)

This note describes the type-class extension of Sparcl (branch
`type-class`, with higher-kinded classes on branch `higher-kinded`): what
can be written, how it is checked and executed, and its current
limitations. The examples are taken from `Examples/Class*.sparcl`,
which are type-checked and evaluated by the test suite.

Instances are passed as **implicit instance arguments**, as in Agda and
Lean, rather than through Haskell-style constraints (`Eq a => ...`). An
instance argument is written `{{C a}}` in a type; callers usually omit it,
and the type checker inserts it by instance search. At run time an
instance is an ordinary value, a *dictionary* holding the methods.


Overview
--------

```
class Eq a where
    sig (==) : a -> a -> Bool
    sig (/=) : a -> a -> Bool
    fixity == 40
    fixity /= 40
    def (/=) x y = not (x == y)        -- default method
end

instance eqNat : Eq Nat where           -- a named instance
    def (==) Z     Z     = True
           | (S n) (S m) = n == m
           | _     _     = False
end

instance eqList : {{Eq a}} -> Eq (List a) where   -- an instance with an argument
    def (==) Nil         Nil         = True
           | (Cons x xs) (Cons y ys) = and (x == y) (xs == ys)
           | _           _           = False
end

sig elem : {{Eq a}} -> a -> List a -> Bool
def elem _ Nil         = False
       | x (Cons y ys) = case x == y of
                           True  -> True
                         | False -> elem x ys
                         end

def t3 = Cons 1 (Cons 2 Nil) == Cons 1 (Cons 2 Nil)   -- uses eqList and Eq Int
def t8 = elem {{eqNat}} Z (Cons (S Z) (Cons Z Nil))   -- an instance passed explicitly
```


Syntax
------

### Class declarations

    class C a1 ... an [extends S1, ..., Sm] [where
        sig m : t          -- method signatures
        fixity op k        -- fixities of operator methods
        def m ... = ...    -- default implementations (optional)
    end]

* A class may have several parameters (`class Convert a b`), and a method
  need not be a function (`sig mempty : a`).
* Superclasses are listed after `extends`, e.g. `class Ord a extends Eq a`.
  An instance of `Ord T` contains an instance of `Eq T`, so `{{Ord a}}` also
  provides the methods of `Eq a`. Cyclic superclasses are allowed.
* A default method may use the other methods of the class (and defaults may
  be defined in terms of each other, as `leq` and `compare` in
  `Examples/ClassOrd.sparcl`).
* Method signatures may mention the class parameters, which are not
  quantified in them. A method `sig m : t` of `class C a` has the type
  `forall a .... {{C a}} -> t`, with all quantifiers in front.

### Instance declarations

    instance [x :] {{H1}} -> ... -> {{Hk}} -> C t1 ... tn [where
        def m ... = ...
    end]

* The name `x` is optional; it is needed only to pass the instance
  explicitly. An unnamed instance gets a generated name.
* `{{H1}} -> ... ->` are the instance's own instance arguments, e.g.
  `instance {{Eq a}} -> {{Eq b}} -> Eq (Pair a b)`. They are available as
  local instances in the method bodies.
* A method without a definition takes its default; a method with neither
  is an error.
* A method body is checked against the method signature with the class
  parameters replaced by the arguments of the instance head. Method bodies
  may use the top-level definitions, also those without signatures.

### Instance arguments

* **Types.** `{{C t1 ... tn}} -> t` is a function type whose argument is an
  instance. Instance arrows are always unrestricted (`Omega`), whatever the
  rest of the type is, so a dictionary can be used any number of times. The
  contents of `{{ }}` must be a class applied to all its parameters (of
  kind `Type`).
  Instance arguments cannot be named in types.
* **Expressions.** `f {{e}}` passes an instance explicitly. `{{e}}` can be
  written only as an argument of an application (not parenthesized, not as
  an expression of its own).
* **Patterns.** `def f {{d}} x = ...` and `\{{d}} x -> ...` bind an instance
  argument by name (`{{_}}` binds it without a name). Instance patterns are
  allowed only as argument patterns of `def` and `\`, their contents are a
  variable or `_`, and all clauses of a definition must have them at the
  same positions. Binding them is optional: an unbound instance argument is
  still used implicitly in the body.
* **Class types as ordinary types.** A class applied to types is a type,
  and instances are values of that type: `sig d : Eq Nat; def d = eqNat`.


Semantics
---------

### Insertion of instance arguments

The type checker inserts the instance arguments that are not written:

* **Abstractions.** When an expression is checked against `{{C}} -> t`, an
  abstraction `\{{d}} -> ...` is inserted, and `d` is a local instance in
  the expression. (Not for an expression that binds the instance itself
  with `\{{p}} -> ...`, nor for parentheses and type annotations, which
  pass the type inside.)
* **Patterns.** The argument patterns of a `def` clause or of `\` are
  aligned with the arrows of its type; an instance arrow without a written
  `{{p}}` gets an inserted instance pattern. All clauses of a definition
  share the inserted variable, so that desugaring can still group clauses
  with invertible patterns into one invertible `case`.
* **Applications.** In an application, an instance arrow of the function's
  type without a written `{{e}}` gets an inserted instance argument, to be
  found by instance search. Instance arrows after the last argument are
  also filled when the application is checked against a known type, and
  when it is the bound expression of `let p <- e in ...` or the scrutinee of
  `case`; an expression whose type is only inferred keeps them (for
  example, `:type elem` in the REPL shows
  `forall a. {{Eq a}} -> a -> List a -> Bool`).

A top-level definition without a signature never gets instance arguments
by inference: its instance arguments must be solvable inside its body.
For example, `def g x y = x == y` needs a signature such as
`sig g : {{Eq a}} -> a -> a -> Bool`.

### Instance search

Each inserted instance argument becomes a *goal* `C t1 ... tn`. Goals of a
group of definitions are solved after its bodies are checked (when more of
their types is known) and before generalization.

1. **Local instances** are tried first: variables bound by `{{d}}` or by
   inserted abstractions, then their superclasses (by projections), inner
   ones before outer ones. The first one that matches the goal is taken.
2. Otherwise, **global instances** (instance declarations) are tried. The
   instance whose head matches the goal is taken, and its own instance
   arguments become subgoals. Several matching global instances are an
   error; instances may overlap, but a goal they both match is ambiguous.

Search never instantiates type variables of the goal that are still
unknown. A goal that cannot be decided yet is postponed (to the enclosing
definition, for a local definition); one that stays undecided at the top
level is reported as ambiguous. Search has a depth limit, so cyclic
instance declarations are reported rather than looping.

When an instance is declared, its superclass instances must be found, with
its own instance arguments as local instances.

### Run time

Desugaring turns classes and instances into ordinary values:

* A **dictionary** of class `C` is a value `<dict C> s1 ... sm f1 ... fn`
  of the superclass dictionaries (in `extends` order) and the methods (in
  signature order).
* A **method** and a **superclass projection** are functions that take a
  dictionary and return one of its fields.
* An **instance** `x : {{H1}} -> ... -> {{Hk}} -> C ts` is a function of its
  instance arguments returning a dictionary, which refers to itself, so
  that omitted methods can be filled by their defaults applied to it.
* An inserted or explicit instance argument is an ordinary argument.
* These values and the definitions of the module form one recursive group.

With cyclic superclasses, dictionaries are cyclic values; they are
evaluated only to weak head normal form when a module is loaded, and the
REPL prints a dictionary as `<dict C>`.

Instance arguments work with Sparcl's invertible features: methods may
have `rev` and linear types, instance bodies may use invertible patterns
and `with`, and functions with instance arguments run both forwards and
backwards (`Examples/ClassInvertible.sparcl`).

### Modules

Classes and instances are not affected by import and export lists: once a
module is loaded (directly or through other modules), its classes and
instances are in scope, and the values that inserted code refers to
(instances, projections, defaults) are kept. See
`Examples/ClassMod{A,B,C}.sparcl`.

### Higher-kinded classes

A class parameter may be of any kind (see `notes/Kinds.md`); its kind is
inferred from the method signatures or written as an annotation
(`class C (f : Type -> Type)`). A class `C` with parameters of kinds
`k1 ... kn` has kind `k1 -> ... -> kn -> Type`, so applying it to
arguments of the wrong kinds or to the wrong number of arguments is a kind
error.

```
class Functor f where
    sig fmap : (a -> b) -> f a -> f b      -- f : Type -> Type
end

class Applicative f extends Functor f where
    sig pure : a -> f a
    sig ap   : f (a -> b) -> f a -> f b
end

instance Functor (Either e) where          -- a partial application
    def fmap _ (Left e)  = Left e
           | g (Right x) = Right (g x)
end

sig liftA2 : {{Applicative f}} -> (a -> b -> c) -> f a -> f b -> f c
def liftA2 g x y = ap (fmap g x) y
```

No special machinery is involved: the method types of an instance are
obtained by substituting the head arguments for the class parameters
(`f a` becomes `Either e a`), and instance search uses the same rules,
with type applications unified argument by argument. Instance heads may be
partial applications (`Functor (Either e)`), `rev`
(`instance RevMap rev`), or have applied variables
(`instance {{Functor f}} -> Size (f Int)`). Every
type variable of an instance type must occur in its head. See
`Examples/ClassFunctor.sparcl` and `Examples/ClassHigherKinded.sparcl`.


Errors
------

| Situation | Message |
| --- | --- |
| no instance for a goal | `No instance found for ...` |
| several global instances match a goal | `Several instances match ...` |
| a goal whose types cannot be determined | `Ambiguous instance argument: ...` |
| a definition without a signature needs an instance argument | `Cannot infer the instance argument ... add a signature.` |
| instance search too deep | `Instance search for ... is too deep` |
| `{{e}}` / `{{p}}` where the type has an ordinary arrow | `An instance argument {{...}} is given where an ordinary argument is expected.` |
| `{{e}}` passed to a function of unknown type | `... cannot be passed to a function whose type is unknown` |
| `{{p}}` where the type is unknown | `An instance pattern {{...}} needs a type annotation.` |
| a non-class inside `{{ }}`, as a superclass or an instance head | `Not a class: ...` |
| a class applied to arguments of wrong kinds or numbers | a kind error (see `notes/Kinds.md`) |
| a type variable of an instance type not in its head | `Type variable ... does not occur in the instance head ...` |
| an instance defines something that is not a method | `... is not a method of the class of instance ...` |
| an instance omits a method without a default | `Instance ... does not define method ...` |
| `{{e}}` outside an argument position | a parse error with a dedicated message |

The error cases are in `Nonexamples_Illtyped/Class*.sparcl`.


Limitations
-----------

* **No kind polymorphism.** A class parameter has one kind; a kind not
  determined by the method signatures defaults to `Type`. Function types
  cannot be instance heads without their arguments (there is no
  `instance Functor ((->) r)`).
* **Signatures for instance arguments.** Definitions without a signature
  do not get instance arguments by inference (see above). A goal whose type
  is fixed by nothing, e.g. the result of `bwd serialize (...)`, needs a
  type annotation.
* **Instance patterns need a known type.** `def f {{d}} x = ...` needs a
  signature, and an abstraction `\{{d}} -> ...` needs a known type; an
  annotation must enclose the whole abstraction:
  `((\{{d}} x -> x == x) : forall a. {{Eq a}} -> a -> Bool)`. Type variables
  in annotations are not quantified implicitly.
* **Trailing instance arguments of a clause.** With
  `sig f : a -> {{Eq a}} -> Bool`, the clause `def f x = ...` does not bind
  the instance argument, so its `where` declarations do not see it; write
  `def f x {{_}} = ...` (`Examples/ClassTrailingWhere.sparcl`).
* **Functions of unknown type.** No instance argument is inserted while the
  type of the applied function is still unknown, so storing functions with
  instance arguments in data structures may need annotations
  (`Examples/ClassInstArgInList.sparcl`).
* Data constructors cannot take instance arguments.


Implementation
--------------

| Phase | Files | Changes |
| --- | --- | --- |
| Syntax | `Surface/Syntax.hs`, `Surface/Parser/Exp.hs` | `DClass`, `DInst`; `{{C}} -> t` as `TInstArr C t` (internally `TyInstFun`); application arguments `Arg = ExplicitArg | InstArg`; pattern `PInst`; the hole `InstHole` made by the type checker |
| Renaming | `Renaming.hs` | classes, instances and instance patterns |
| Type checking | `Typing/Typing.hs`, `Typing/TCMonad.hs`, `Typing/Instance.hs` | class and instance tables; checks of class types; insertion of instance abstractions, patterns and applications (applications are checked as spines); goals and instance search; checking of default methods and instance bodies |
| Desugaring | `Desugar.hs`, `Name.hs` | dictionaries, methods, projections, defaults and instances as Core values (generated names `<dict C>`, `<super C #i>`, `<default m>`) |
| Evaluation | `Value.hs` | dictionaries forced only to weak head normal form, printed as `<dict C>` |
| Modules | `Module.hs` | class and instance tables propagated regardless of import and export lists |
| Kinds | see `notes/Kinds.md` | kinds of classes, kind checking of class types and instance types |

In the surface AST, operator applications (`Op`) do not exist after type
checking (the type checker outputs them as applications), and dictionary
holes (`InstHole`) exist only after it; the pass-indexed tags of these
constructors are `Void` in the other passes. The names generated for
classes are names of the module declaring the class, so that code built in
other modules refers to the same values.

Tests: every file in `Examples/` must type-check and every file in
`Nonexamples_Illtyped/` must be rejected; for the class examples,
`test/Spec.hs` also compares each test binding `tK` with its expected value
`tK'` written in the example.
