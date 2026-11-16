Kinds and Higher-Kinded Types in Sparcl
=======================================

This note describes the kind system of Sparcl (branch `higher-kinded`):
type-level expressions may be applied to arguments whatever their head
is, every type-level expression has a kind, and kinds are inferred and
checked. This makes higher-kinded type variables and higher-kinded type
classes (such as `Functor`) possible; classes are described in
`notes/TypeClasses.md`. The examples are taken from `Examples/Kind*.sparcl`
and `Examples/Class{Functor,HigherKinded}.sparcl`, which are type-checked
and evaluated by the test suite.


Kinds
-----

    kind ::= Type | Multiplicity | kind -> kind | ( kind )

* `Type` is the kind of types of values (`Int`, `List Int`, `a -> b`).
* `Multiplicity` is the kind of multiplicities (`One`/`1`, `Omega`/`ω`,
  and multiplicity variables), which appear after `#` in function types
  and in constraints.
* `k1 -> k2` is the kind of type-level functions; the arrow is right
  associative. For example, with `data List a = ...` and
  `data Either a b = ...`, `List : Type -> Type` and
  `Either : Type -> Type -> Type`; the built-in `Many` has kind
  `Multiplicity -> Type -> Type`.
* There is no kind polymorphism: a kind that is not determined by the uses
  defaults to `Type`.
* `Type` and `Multiplicity` are reserved words.

Built-in kinds: `Int`, `Char`, `Bool`, `Rational` : `Type`;
`Un`, `rev` : `Type -> Type`; `Many` : `Multiplicity -> Type -> Type`;
tuple types of all sizes, e.g. `(a, b)` : `Type -> Type -> Type`.


Type-level expressions
----------------------

* **Applications with any head.** A type variable may be applied
  (`f a`), and so may a parenthesized expression (`(Either Bool) Int`).
  Whether an application makes sense is decided by kinds, not by the
  syntax: `(a -> b) c` parses and is a kind error.
* **Higher-kinded type variables** may be used wherever types are written:
  signatures, annotations, higher-rank types, parameters of data types,
  synonyms and classes, GADT-style constructors and instance types.

      data Fix f = In (f (Fix f))                -- f : Type -> Type
      data Compose f g a = MkCompose (f (g a))   -- f, g : Type -> Type

      sig applyTwice : (f Int -> f Int) -> f Int -> f Int

* **`rev` is an ordinary type constructor** of kind `Type -> Type` and can
  be passed without its argument: `data Box f = MkBox (f Int)` and
  `sig unBox : Box rev -o rev Int`.
* **Function types are not applications.** `a # m -> b` (including `->`
  and `-o`) and `{{C}} -> t` are constructs of their own, as in Agda and
  Lean: they cannot be written without their arguments (there is no
  `(->) r`), and a type application never matches them (`f b` does not
  unify with `Int -> Int`). Their kinding rules are: `a # m -> b : Type`
  for `a, b : Type` and `m : Multiplicity`; `{{C}} -> t : Type` for
  `C, t : Type`.
* **Synonyms** may be applied to more arguments than their parameters
  (`type F = Maybe` makes `F Int` valid; `type G a = Maybe` makes
  `G Bool Int` valid), but not to fewer. The body of a synonym may be of
  any kind.


Kind annotations
----------------

Kinds are inferred, but may be written:

* on parameters of data types, synonyms and classes:
  `data T (f : Type -> Type) = MkT (f Int)`, `class Default (a : Type)`;
* on `forall` binders, in signatures, annotations and GADT-style
  constructor signatures:
  `sig idK : forall (f : Type -> Type) a. f a -> f a`,
  `sig idM : forall (p : Multiplicity) a. a # p -> a`;
* on type-level expressions: `(Maybe : Type -> Type) Int`.

Implicitly quantified type variables (those without a `forall`) cannot be
annotated.


Kind inference and checking
---------------------------

* **Declarations.** The kinds of data types, synonyms and classes are
  inferred together for each group of mutually dependent declarations,
  dependencies first; kinds left undetermined in a group default to
  `Type`. For example, `data M p = MkM (Many p Int)` gives
  `M : Multiplicity -> Type`, while in
  `data P a = MkP` the parameter defaults to `a : Type`, so a later
  `P Maybe` is a kind error.
* **Written types.** Signatures, annotations, instance types, fields,
  superclasses and method signatures are checked to be of kind `Type`
  (multiplicities after `#` of kind `Multiplicity`).
* **Unification preserves kinds.** A type variable or a meta variable is
  bound only to a type-level expression of its kind. A type application
  `f a` unifies with another application argument by argument, so
  `?f ?a ~ Either Bool Int` gives `?f := Either Bool` and `?a := Int`.
* **Modules.** The kinds of the type-level names that a module exports, or
  that the types of its exported values mention, are kept when it is
  imported.


Higher-kinded classes
---------------------

Classes need no special treatment: a class parameter may have any kind,
inferred from the method signatures, and instances may be given for
partial applications, for `rev`, or with applied variables in their heads.

```
class Functor f where
    sig fmap : (a -> b) -> f a -> f b      -- f : Type -> Type
end

instance Functor (Either e) where
    def fmap _ (Left e)  = Left e
           | g (Right x) = Right (g x)
end

sig inc : {{Functor f}} -> f Int -> f Int
def inc = fmap (\x -> x + 1)
```

See `notes/TypeClasses.md` and `Examples/ClassFunctor.sparcl`,
`Examples/ClassHigherKinded.sparcl`.


Errors
------

| Situation | Message |
| --- | --- |
| a kind different from the expected one | `Kinds do not match: ... has kind ...` |
| something not of a function kind applied to arguments | `Applied to arguments, but its kind is not of the form k1 -> k2: ...` |
| a synonym applied to fewer arguments than its parameters | `Type synonym "G" must be fully-applied.` |
| `Type` / `Multiplicity` used as a name | a parse error |

A kind error in a written type stops type checking. The error cases are
in `Nonexamples_Illtyped/Kind*.sparcl`.


Implementation
--------------

| Part | Files | Changes |
| --- | --- | --- |
| Surface syntax | `Surface/Syntax.hs`, `Surface/Parser/Exp.hs` | binary applications `TApp` of nullary `TCon` / `TVar`; parentheses kept (`TParens`); function types `TArr` / `TInstArr`; kind annotations `(t : k)` (`TKind`) and binders `TyBinder x (Maybe kind)`; a parser for kinds (`kindExpr`) |
| Internal types | `Typing/Type.hs` | binary `TyConst` / `TyApp`, with `TyCon c ts` as a pattern synonym for a spine headed by a constant; function types `TyFun` / `TyInstFun`; kinds reuse `Ty` (`typeKi`, `multKi`, `arrKi`); type variables and meta variables carry their kinds; `kindOf`, `kindOfName` |
| Kind checking | `Typing/Typing.hs`, `Typing/TCMonad.hs` | kind inference of declarations (`inferTyDeclKinds`); conversion of written types with kind checking (`ty2ty`, `convertWrittenTy`); kind-preserving unification (`checkBindKind`, `unifyKind`); kinds in instantiation and generalization |
| Instance search | `Typing/Instance.hs` | binary, kind-preserving unification in `unifyPure` |
| Modules | `Module.hs` | kinds of type-level names in the type table; kinds of reachable names kept by import and export lists |

Tests: besides the samples, `test/Spec.hs` has unit tests of internal
functions (binary unification, `unifyPure`, `kindOf`, instantiation and
generalization with kinds).
