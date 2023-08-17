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
But this doesn't capture the *whole* meaning: the `Semigroup` supertype tells us that `Pair` has a join method, but it doesn't tell us that it can accept other pairs.
We could try to specify that it's a semigroup on pairs:
```
subtype Pair <: Semigroup { type T = Pair }
```
The above isn't grammatically valid in Nominal Wyvern though, and it's still missing a subtle piece of information: the pair we pass to the semigroup has to be the *same* pair.


There's some missing context that we can't see from looking at the shape definition in isolation: these shapes all expect their type member to be instantiated with the type itself to "tie the recursive knot".
If we're designing a whole new programming language with shapes in mind, could we make it nicer to express such use-cases?

* `ThisType` for Object-Oriented Languages: From Theory to Practice SUKYOUNG RYU, KAIST

We could introduce special `self.TYPE` syntax for referring to ThisType inside shapes:

```
shape Cloneable { self =>
  def clone(): self.TYPE
}

shape Equatable { self =>
  def equals(that: self.TYPE): Bool
}

shape Semigroup { self =>
  def join(that: self.TYPE): self.TYPE
}
```

To clean up the explicit recursion during type member definitions `type A <= Semigroup { TYPE = self.A }`, we also define a special syntax for shape type-members.
A shape type-member `shape type A <= Semigroup` has the semantics `type A <= Semigroup { TYPE = self.A }`.
It's nice syntactic sugar, but more importantly, it ensures that recursion can only happen in certain specific decidable cases with only a local rule.

```
name Pair { self =>
  shape type A <= Semigroup
  shape type B <= Semigroup
  def join(that: self.TYPE): self.TYPE
}
```

We can now ban cycles in the subtyping dependency graph altogether.
We also need to ban self.TYPE from occurring in type members, eg `type DUP = Pair { A = self.TYPE; B = self.TYPE }` is not allowed, because the pseudo-member `TYPE` depends on `DUP`.


We can also describe conditionally-cloneable sets now, too:
```
subtype Set { shape type Elem <= Cloneable } <: Cloneable
```

(Although, we still don't have a way to conditionally add the implementation of Cloneable.)

## Examples

Side question: how to express monoid typeclass, which has a zero-element, with a shape-style interface?
We can implement a Dictionary with a type member and methods for the non-member operations:
```
name MonoidDict { self =>
  shape type A <= Semigroup
  def zero(): A
}
```

How do you express collections of semigroups?
In Nominal Wyvern we need a top-level member, something like:
```
name Set { self =>
  type ElemT
  def index(i: Int): Option { T = self.ElemT }
}

name Collector { self =>
  type T <= Semigroup { type TYPE = self.T }
  def collect(s: Set { type ElemT = self.T }):
    self.T
}
```

With the `shape type` syntax in refinements we can write it as a path-dependent method:
```
  def collect(s: Set { shape type T <= Semigroup }):
    s.T
```

The `shape type` here is important, because it makes sure s.T is the actual result of the semigroup operation.
Without it, the result of joining the semigroups together would be the `Semigroup::TYPE` of some value nested inside the set.

Decidable Wyvern could also express it as a path-dependent method using recursive refinements:
```
  def collect(s: Set { set => type T = Semigroup { type TYPE = set.T } }):
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
  τ      := β r
            (refined types)
```

Type members:
```
  member := `shape`? `type` t B τ
```

Anonymous refinements:
```
  r      := { member... }
```

Type declarations:
```
  method := `def` m(x: τ): τ' = e
  D0     := (`name` | `shape`) n { x => member... method... }
  D      := D0...
```

Subtyping declarations:
```
  S      := `subtype` n r <: n
```

Terms
```
  p      := x | p.v
            (paths)
```

# Helpers

## Member lookup
Judgment form
```
Γ ⊢ member ∈ₓ n
```

```
x: τ ∈ Γ
----------------------- (MemTypeTYPE)
Γ ⊢ type TYPE <= τ ∈ₓ n
```

```
Δ(n) = { x => ...type t B τ... }
-------------------------------- (MemType)
Γ ⊢ type t B τ ∈ₓ n
```

```
Δ(n) = { x => ...shape type t B τ... }
-------------------------------- (MemShape)
Γ ⊢ type t B τ { type TYPE = x.t } ∈ₓ n
```


## Exposure
Paths:
```
x: τ ∈ Γ     Γ ⊢ τ ↑ β { ...;type t LEQ τ';... }     Γ ⊢ τ' ↑ τ''
----------------------------------------------------------------- (XPathRefine)
Γ ⊢ x.t ↑ τ''

x: τ ∈ Γ     Γ ⊢ τ ↑ β { ...;shape type t LEQ τ';... }     Γ ⊢ τ' ↑ τ''
----------------------------------------------------------------- (XPathRefineShape)
Γ ⊢ x.t ↑ τ'' { type TYPE = x.t }

x: τ ∈ Γ     Γ ⊢ τ ↑ n r   t ∉ r    type t LEQ τ' ∈ₓ Δ(n)       Γ ⊢ τ'  ↑ τ''
----------------------------------------------------------------------------- (XPathDef)
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

x: τ ∈ Γ     Γ ⊢ τ ↑ β { ...;shape type t GEQ τ';... }
------------------------------------------------ (DCMemberShape)
Γ ⊢ x.t ↑- τ' { type TYPE = x.t }

x: τ ∈ Γ     Γ ⊢ τ ↑ n r     t ∉ r     type t GEQ τ' ∈ₓ Δ(n)
------------------------------------------------------------ (DCDef)
Γ ⊢ x.t ↑- τ'
```

If the type of `x` exposes to bottom, it basically means the environment is garbage (falso), and we can prove anything.
So, we downcast to top which will make the subtyping trivially true.
```
x: τ ∈ Γ     Γ ⊢ τ ↑  ⊥
---------------------- (DC⊤)
Γ ⊢ x.t ↑- ⊤
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

# Top-level rules
The top-level rules for `shape type` members need to unfold the recursion one step, but otherwise are pretty similar to the Nominal Wyvern rules.

# Example typing derivations

Given type definitions:
```
shape Semigroup { self =>
  def join(that: self.TYPE): self.TYPE
}

name PlusInt { self =>
  def join(that: PlusInt): PlusInt
  val i: Int
}

name Pair { self =>
  shape type A <= Semigroup
  shape type B <= Semigroup
  def join(that: Pair { self.A; self.B }): Pair { self.A; self.B }
  val a: self.A
  val b: self.B
}
```

To check declared subtyping relation: `subtype PlusInt <: Semigroup`
```
Σ = PlusInt <: Semigroup

Δ | Σ ⊢ PlusInt <: Semigroup
---> (top-level)
x: PlusInt ⊢ { def join(that: PlusInt): PlusInt; val i: Int } <: { def join(that: x.TYPE): x.TYPE }
---> (by σ)
  def join(that: PlusInt): PlusInt <= def join(that: x.TYPE): x.TYPE
  ---> (by method)
    x: PlusInt                ⊢ PlusInt <: x.TYPE
    ---> (SubMemberUpper)
      stuck????

    x: PlusInt, that: PlusInt ⊢ x.TYPE <: PlusInt
    ---> (SubMemberLower)
      x: PlusInt, that: PlusInt ⊢ PlusInt <: PlusInt
      ---> (SubRefl).
```

We get stuck trying to show `x: PlusInt ⊢ PlusInt <: x.TYPE`. In fact, surprisingly (?) it's not even true in a system with subtyping-by-inheritance: if we defined a subtype of `PlusInt` called `PlusInt2` then the inherited method `PlusInt2::join(t: PlusInt): PlusInt` is not a valid `Semigroup::join`.
The `ThisType` paper distinguishes between exact and inexact types.
We can specify the exact type as roughly `PlusInt { type TYPE = PlusInt }` which says that the real runtime value is a `PlusInt`.
With the exact type, we can prove `subtype PlusInt { type TYPE = PlusInt } <: Semigroup`





To check declared subtyping relation: `subtype Pair <: Semigroup`
```
Σ = Pair <: Semigroup

Δ | Σ ⊢ Pair <: Semigroup
-->
x: Pair ⊢ {
  type A <= Semigroup { type TYPE = x.A };
  type B <= Semigroup { type TYPE = x.B };
  def join(that: Pair { x.A; x.B }): Pair { x.A; x.B };
  val a: x.A;
  val b: x.B;
} <: {
  def join(that: x.TYPE): x.TYPE
}
```
