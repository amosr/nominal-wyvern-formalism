# Motivation
In Nominal Wyvern and Decidable Wyvern, shapes are the only places where cycles are allowed.
The shapes I've seen have a pretty similar structure:

```
@shape name Cloneable { self =>
  type CT <= Top // covariant
  def clone(): CT
}

@shape name Equatable { self =>
  type EQ <= Top // contravariant
  def equals(that: EQ): Bool
}

@shape name Semigroup { self =>
  type T <= Top // invariant
  def join(that: T): T
}
```

These shapes aren't very meaningful on their own: if I have a type `T <: Cloneable`, I know it has a clone method, but I don't know what it will return.
To get more information, we need to further refine the use of shapes: `T <: Cloneable { type CT = T }`.
We have a similar situation in Java, where we must define a generic parameter to be `<T extends Cloneable<T>>`.

Writing an instance for a pair semigroup is a bit tedious:
```
name Pair { self =>
  type A <= Semigroup { A = self.A }
  type B <= Semigroup { A = self.B }
  type T  = Pair { A = self.A; B = self.B }
  def join(that: Pair { self.A; self.B }): Pair { self.A; self.B }
}
```

And we can't really say that Pair is a semigroup.
We can write:
```
subtype Pair <: Semigroup
```
The above doesn't exactly capture the meaning: the `Semigroup` supertype tells us that `Pair` has a join method, but it doesn't tell us that it can accept other pairs.
We could try to specify that it's a semigroup on pairs:
```
subtype Pair <: Semigroup { type T = Pair }
```
The above isn't grammatically valid in Nominal Wyvern though, and it's still missing a subtle piece of information: the pair we pass to the semigroup has to be the *same* pair.


There's some missing context that we can't see just looking at the shape definition itself: these shapes all expect their type member to be instantiated with the type itself to "tie the recursive knot".
If we're designing a whole new programming language with shapes in mind, could we make it nicer to express such use-cases?

* `ThisType` for Object-Oriented Languages: From Theory to Practice SUKYOUNG RYU, KAIST

```
name Cloneable { self =>
  def clone(): type[self]
}

name Equatable { self =>
  def equals(that: type[self]): Bool
}

name Semigroup { self =>
  def join(that: type[self]): type[self]
}

name Pair { self =>
  type A <= Semigroup
  type B <= Semigroup
  def join(that: type[self]): type[self]
}
```

If we only allow this special `type[p]` path types in method and field declarations, then we can ban cycles altogether.
Does this simplify the metatheory and decidability?

No: this doesn't work because `Semigroup` is invariant. We can't take a `adder: PlusInt` and cast it to a `Semigroup` and then call join with other semigroups.
Ie, if `adder: Semigroup` and we try to call `adder.join`, the `type[adder]` should not reduce to `Semigroup`.

What if we had a `fix` combinator for types?
We could define the shapes as before and write `fix[T] Semigroup` as shorthand for `µ t. Semigroup { type T = t }`.
Then we could implement Pair-semigroup as:
```
name Pair { self =>
  type A <= fix Semigroup
  type B <= fix Semigroup
  type T  = Pair { A = self.A; B = self.B }
  def join(that: Pair { self.A; self.B }): Pair { self.A; self.B }
}
```
Which is slightly cleaner than the Nominal Wyvern definition.
We need to be able to write fix on the right-hand-side of declared subtyping relations too:

```
subtype Pair <: fix Semigroup
```

We can also describe conditionally-cloneable sets now, too:
```
subtype Set { type Elem <= fix Cloneable } <: fix Cloneable
```

(Although, we still don't have a way to conditionally add the implementation of Cloneable.)

## Examples

Side question: how to express monoid typeclass, which has a zero-element, with a shape-style interface?
Dictionary-style with type members still works:
```
name MonoidDict { self =>
  type A
  def zero(): A
  def join(this: A, that: A): A
}
```
Or maybe:
```
name MonoidDict { self =>
  type A <= Semigroup
  def zero(): A
}
```

How do you express collections of semigroups?
In Nominal Wyvern we need a top-level member, something like:
```
name Set { self =>
  type T
  def index(i: Int): Option { T = self.T }
}

name Collector { self =>
  type T <= Semigroup { type T = self.T }
  def collect(s: Set { type T = self.T }):
    self.T
}
```

With explicit fixpoints we can write it as a path-dependent method:
```
  def collect(s: Set { type T = fix Semigroup }):
    s.T
```

Decidable Wyvern could also express it as a path-dependent method:
```
  def collect(s: Set { set => type T = Semigroup { type T = set.T } }):
    s.T
```


# Grammar

Variables:
```
  x... value variables
  t... type variables
```

Variance declarations:
```
  B      := `<=` | `>=` | `=`
  LEQ    := `<=` | `=`
  GEQ    := `>=` | `=`
```

Types:
```
  β      := `⊤` | `⊥` | n |  x.t
            (base types)
  τ      := β r | `fix`[t] n
            (refined and fixed types: for now, limit fixpoints to names without refinements)
```

Type members:
```
  member := `type` t B τ
```

Anonymous refinements:
```
  r      := { member... }
```

Type declarations:
```
  method := `def` m(x: τ): τ' = e
  D0     := `name` n { x => member... method... }
  D      := D0...
```

Subtyping declarations:
```
  S      := `subtype` n r <: n_fix
  n_fix  := n | `fix`[t] n
```

Terms
```
  p      := x | p.v
            (paths)
```

# Helpers

## Exposure
Exposure just leaves fixpoints alone.
It's tempting to unfold the fixpoint once, eg `fix[t] n ↑ n { type t = fix[t] n }`, but this could lose some information about the identity of the fixpoint.
Because there are many potential implementations of fixpoints, if we have two semigroups in scope `x, y: fix Semigroup` then we don't know that `x.t = y.t`.
So, unfolding `x: fix Semigroup` to `Semigroup { type t = fix Semigroup }` might lose the fact that `x.t` should be the exact same semigroup as `x`.


Paths:
```
x: τ ∈ Γ     Γ ⊢ τ ↑ β { ...;type t LEQ τ';... }     Γ ⊢ τ' ↑ τ''
----------------------------------------------------------------- (XPathRefine)
Γ ⊢ x.t ↑ τ''

x: τ ∈ Γ     Γ ⊢ τ ↑ n r   t ∉ r    type t LEQ τ' ∈ Δ(n)[this := x]       Γ ⊢ τ'  ↑ τ''
--------------------------------------------------------------------------------------- (XPathDef)
Γ ⊢ x.t ↑ τ''
```


Do we need this rule:?
If the type of `x` exposes to bottom, it basically means the environment is garbage (falso), and we can type (prove) anything.
We expose `x.t` to bottom too:
```
x: τ ∈ Γ    Γ ⊢   τ ↑ ⊥
----------------------- (XPath⊥)
            Γ ⊢ x.t ↑ ⊥
```

Otherwise, exposure returns the type as-is:
```
τ not path
---------- (XId)
Γ | τc ⊢ τ ↑ τ
```

Exposure should satisfy `Γ ⊢ τi ↑ τo` implies `Γ ⊢ τi <: τo`.
Exposure should be terminating for well-formed contexts and if all type definitions are acyclic.
Exposing a path `Γ ⊢ x.t ↑ τo` cannot return `τo` as `x.t` or `x.t r`, but it could return a refined shape that refers to x.t, eg `n { t = x.t }`

## Downcast

Downcast `Γ ⊢ τ ↑- τ'` is used for member lookups on the right-hand-side, like in D-sub. It's not recursive and only uses exposure, so is total and terminating.

For paths `x.t`, we expose the type of `x` and try to get the member lower-bound from the refinement.
If it's not in the refinement, we look in the named type definition:
```
x: τ ∈ Γ     Γ ⊢ τ ↑ β { ...;type t GEQ τ';... }
------------------------------------------------ (DCMember)
Γ ⊢ x.t ↑- τ'

x: τ ∈ Γ     Γ ⊢ τ ↑ n r     t ∉ r     type t GEQ τ' ∈ Δ(n)[this := x]
---------------------------------------------------------------------- (DCDef)
Γ ⊢ x.t ↑- τ'
```

If the type of `x` exposes to bottom, it basically means the environment is garbage (falso), and we can prove anything.
So, we downcast to top which will make the subtyping trivially true.
```
x: τ ∈ Γ     Γ ⊢ τ ↑  ⊥
---------------------- (DC⊤)
Γ ⊢ x.t ↑- ⊤
```


Type of path looks like it should be easy, but it's not clear whether we should recursively downcast τ or expose it:
```
x: τ ∈ Γ   Γ ⊢ τ ↑- τ'
--------------------- (XTypePath)
Γ ⊢ type[x] ↑- τ'
```

Hu & Lhotak (2020) has a failover case that goes to bottom, I don't think it's strictly necessary:
```
  ...if no other x.t rules apply
--------------------- (DC⊥)
Γ ⊢ x.t ↑- ⊥
```

Otherwise, return the type as-is:
```
τ not path
---------- (DCId)
Γ ⊢ τ ↑- τ
```


# Subtyping

Judgment form for type subtyping, `Γ ⊢ τ <: τ'`, uses auxiliary judgment forms `Γ ⊢ r <: r'`.

## Core rules
```
  ------------------- (Sub⊤)
  Γ ⊢ τ <: ⊤

  ------------------- (Sub⊥)
  Γ ⊢ ⊥ <: τ

  Γ ⊢   r <:   r'
  -------------------- (SubRefine)
  Γ ⊢ τ r <: τ r'

  n r' <: n' ∈ S     Γ ⊢ r <: r'     Γ ⊢ n' (r' + r) <: n'' r''
  --------------------------------------------------------- (SubNameUp)
  Γ ⊢ n r <: n'' r''
```

## Member lookup rules
```
  Γ ⊢ x.t ↑  τ     Γ ⊢ τ <: τ'
  ----------------------------------------------------- (SubMemberLower)
  Γ ⊢ x.t <: τ'

  Γ ⊢ x.t ↑- τ'     Γ ⊢ τ <: τ'
  ----------------------------------------------------- (SubMemberUpper)
  Γ ⊢ τ <: x.t
```

Should these rules allow refinements on the variable? Decidable Wyvern doesn't.

## Fixpoint rules

We treat each case `fix <: fix`, `n <: fix` and `fix <: n` as a separate rule.
This lets us simplify the rules a bit.
If we imagine that there is some denotational semantics of what subtyping should be, then our subtyping rules aim to be a sound under-approximation of this denotational semantics.
It's OK if the rules disallow some subtyping relations that might hold on an ideal (but undecidable) system.

To compare two fixpoints, the rule `Γ ⊢ fix[t] n <: fix[t] n'` just checks that the two underlying types are subtype-equivalent, ie `n <: n'` and `n' <: n`.
We could probably get away with a rule that only allows reflexivity: `Γ ⊢ fix[t] n <: fix[t] n`.
```
  Γ ⊢        n <:, :> n'
  ------------------------ (SubFixFix)
  Γ ⊢ fix[t] n <: fix[t] n'
```

It might be able to express a more expressive rule that looks a bit like the following, but I'm not totally sure if it's legit:
```
  Γ ⊢ n { type t = n } <: n' { type t = n }
  --------------------------------------------------- (SubFixFix*BAD)
  Γ ⊢ fix[t] n <: fix[t] n'
```

The rule for a fixpoint on the right-hand-side has a few pieces to it.
Conceptually, we want to unroll the fixpoint and check that the left-hand-side is a subtype of the right-hand-side:
```
  Γ ⊢ n r <: n' { type t = n r }
  -------------------------------------------------------------------------- (SubFixUpper*BAD)
  Γ ⊢ n r <: fix[t] n'
```
But the above isn't so easy to prove decidable because the type is not decreasing / structurally recursive.
Can we break it apart into smaller pieces:?
```
  Γ         ⊢ n r <: n'
  Γ         ⊢ type t B τ ∈ₓ n r
  Γ, x: n r ⊢ type t B τ <: type t = n r
  -------------------------------------------------------------------------------- (SubFixUpper)
  Γ         ⊢ n r <: fix[t] n'
```

The rule for a fixpoint on the left-hand-side is similar: we want to unroll the fixpoint and check.
```
  Γ ⊢ n { type t <= n } <: n' r
  ----------------------------------------------------- (SubFixLower*BAD)
  Γ ⊢         fix[t] n <: n' r
```

We're implicitly applying transitivity here to simplify the rule and make it easier to check (but less complete).
We can first unfold the fixpoint to `n { type t <= fix[t] n }`, then use the (unproven) fact that `fix[t] n <: n` to result in `n { type t <= n }`.


## Auxiliary rules
```
  -------------------- (SubRefNil)
  Γ ⊢ r <: []

  type t = τL ∈ r     Γ ⊢ τL <:,:> τR      Γ ⊢ r <: r'
  ----------------------------------------------------------------------- (SubRefConsEq)
  Γ ⊢ r <: type t = τR, r'

  type t LEQ τL ∈ r     Γ ⊢ τL <: τR    Γ ⊢ r <: r'
  ---------------------------------------------------------------- (SubRefConsLe)
  Γ ⊢ r <: type t <= τR, r'

  type t GEQ τL ∈ r     Γ ⊢ τR <: τL    Γ ⊢ r <: r'
  ---------------------------------------------------------------- (SubRefConsGe)
  Γ ⊢ r <: type t >= τR, r'
```


## Derived rules and properties

No explicit variable reflexivity rule: this is subsumed by `SubRefine`, if we assume that `x.t` is syntactic sugar for `x.t {}` (with no refinements):
```
  ------------------------ (SubRefNil)
  Γ ⊢     {} <:     {}
  ------------------------ (SubRefine)
  Γ ⊢ x.t {} <: x.t {}
```


# Example typing derivations

Given type definitions:
```
shape Semigroup { self =>
  type T <= Top
  def join(that: self.T): self.T
}

name PlusInt { self =>
  type T = PlusInt
  def join(that: PlusInt): PlusInt
  val i: Int
}

name Pair { self =>
  type A <= fix Semigroup
  type B <= fix Semigroup
  type T  = Pair { A = self.A; B = self.B }
  def join(that: Pair { self.A; self.B }): Pair { self.A; self.B }
  val a: self.A
  val b: self.B
}
```

To check declared subtyping relation: `subtype PlusInt <: fix Semigroup`
```
Σ = PlusInt <: fix Semigroup

Δ | Σ ⊢ PlusInt <: fix Semigroup
---> (top-level)
x: PlusInt ⊢ { type T = PlusInt; def join(that: PlusInt): PlusInt; val i: Int } <: { type T <= fix Semigroup; def join(that: x.T): x.T }
---> (by σ)
  type T = PlusInt <: type T <= fix Semigroup
  ---> (by Σ).

  def join(that: PlusInt): PlusInt <= def join(that: x.T): x.T
  ---> (by method)
    x: PlusInt                ⊢ PlusInt <: x.T
    ---> (SubMemberUpper)
      x: PlusInt              ⊢ PlusInt <: PlusInt
      ---> (SubRefl).

    x: PlusInt, that: PlusInt ⊢ x.T <: PlusInt
    ---> (SubMemberLower)
      x: PlusInt, that: PlusInt ⊢ PlusInt <: PlusInt
      ---> (SubRefl).
```

To check declared subtyping relation: `subtype Pair <: fix Semigroup`
```
Σ = Pair <: fix Semigroup

Δ | Σ ⊢ Pair <: fix Semigroup
-->
x: Pair ⊢ {
  type A <= fix Semigroup;
  type B <= fix Semigroup;
  type T  = Pair { A = x.A; B = x.B };
  def join(that: Pair { x.A; x.B }): Pair { x.A; x.B };
  val a: x.A;
  val b: x.B;
} <: {
  type T <= fix Semigroup; def join(that: x.T): x.T
}
-->
  x: Pair ⊢ type T = Pair { A = x.A; B = x.B } <: type T <= fix Semigroup
  -->
    x: Pair ⊢ Pair { A = x.A; B = x.B } <: fix Semigroup
    -->
      Σ ⊢ Pair <: fix Semigroup

  x: Pair ⊢ def join(that: Pair { x.A; x.B }): Pair { x.A; x.B } <: def join(that: x.T): x.T
  -->
    etc
```
