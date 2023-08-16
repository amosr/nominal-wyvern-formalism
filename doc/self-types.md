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

Such shapes aren't very meaningful on their own: if I have a type `T <: Cloneable`, I know it has a clone method, but I don't know what it will return.
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


There's some missing context that we can't see just looking at the shape definition itself: these shapes all expect their type member to be instantiated with the type itself to "tie the recursive knot".
If we're designing a whole new programming language with shapes in mind, could we make it nicer to express such use-cases?

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
We could define the shapes as before and write `fix Semigroup` as shorthand for `∃ t. Semigroup { type A = t }`.
Then we could implement Pair-semigroup as:
```
name Pair { self =>
  type A <= fix Semigroup
  type B <= fix Semigroup
  type T  = Pair { A = self.A; B = self.B }
  def join(that: Pair { self.A; self.B }): Pair { self.A; self.B }
}
```
Which still isn't great but it's a tiny bit nicer.
If we could write fix in subtyping relations it'd be neat too, as we could describe conditionally-cloneable sets:

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
In Nominal Wyvern:
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
  β      := `⊤` | `⊥` | n |  p1.t | `type`[p]
            (base types)
  τ      := β r
            (refined types)
  p1     := x | l
  p      := p1 | p.v
            (paths)
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
  S      := `subtype` n r <: n'
```

# Helpers

## Exposure
Exposure:

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
x: τ ∈ Γ  Γ ⊢   τ ↑ ⊥
--------------------- (XPath⊥)
          Γ ⊢ x.t ↑ ⊥
```

Type of path is easy:
```
x: τ ∈ Γ   Γ ⊢ τ ↑ τ'
--------------------- (XTypePath)
Γ ⊢ type[x] ↑ τ'
```

Otherwise, exposure returns the type as-is:
```
τ not path
---------- (XId)
Γ ⊢ τ ↑ τ
```

Exposure should satisfy `Γ ⊢ τ ↑ τ'` implies `Γ ⊢ τ <: τ'`.
Exposure should be terminating for well-formed contexts and if all type definitions are acyclic.
Exposing a path `Γ ⊢ x.t ↑ τ'` cannot return `τ'` as `x.t` or `x.t r`, but they could return a refined shape that refers to x.t, eg `n { t = x.t }`

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

Should these rules allow refinements on the variable? Decidable Wyvern doesn't. Unclear whether it would preserve material-shape separation.

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

These rules only look in refinements of the subtype. We could imagine a slightly stronger variant `Γ ⊢ x : τ <: r'` which looks in the type x.t itself, but this would be harder to ensure termination.

## Derived rules and properties

No explicit variable reflexivity rule: this is subsumed by `SubRefine`, if we assume that `x.t` is syntactic sugar for `x.t {}` (with no refinements):
```
  ------------------------ (SubRefNil)
  Γ ⊢     {} <:     {}
  ------------------------ (SubRefine)
  Γ ⊢ x.t {} <: x.t {}
```


# Material-shape separation
Section 3.4, Definition 5 of thesis imposes restrictions:
* Shapes are never lower bounds (after >= or =)
* Upper bound of a shape is always a shape
* Shapes cannot be refined in refinements (but can be refined in top-level type definitions)

## Materials

Judgment form `⊢ τ material` checks whether a type is a material (not a shape):
```
n declared as material
---------------------- (MatName)
⊢ n, n r material

--------------- (MatBase)
⊢ ⊤, ⊥ material
```

<!-- What is the rule for type members `x.t`?
Without extra information, we don't know whether `x.t` is a shape or a material.
Decidable Wyvern has separate type members `x.M` and `x.S` for materials and shapes.
Billy's thesis doesn't describe it, but we can't assume that all variable occurrences are non-material as it rules out too many interesting programs. -->
Can we assume that *all* variable occurrences are material?
```
--------------- (MatVar)
⊢ x.t material
```

## Separation

Top-level judgment form material-shape-separation is written as `⊢ τ ✔️SEP`, uses auxiliary judgment form `⊢ τ ✔️REFINE` for checking inside refinements.
```
⊢ τ   ✔️SEP       ⊢ r ✔️REFINE
---------------------------- (SepRefine)
⊢ τ r ✔️SEP

--------------------- (SepBase)
⊢ ⊤, ⊥, n, x.t ✔️SEP
```

Checking refinements enforces that only materials are allowed as lower bounds:
```
----------------------------- (SepRefNil)
⊢ {} ✔️REFINE

⊢ τ ✔️REFINE       ⊢ r ✔️REFINE
----------------------------- (SepRefConsLe)
⊢ type t <= τ, r ✔️REFINE

⊢ τ ✔️REFINE     ⊢ τ material       ⊢ r ✔️REFINE
---------------------------------------------- (SepRefConsGe)
⊢ type t >= τ, r ✔️REFINE

⊢ τ ✔️REFINE     ⊢ τ material       ⊢ r ✔️REFINE
---------------------------------------------- (SepRefConsEq)
⊢ type t = τ, r ✔️REFINE
```

Checking types inside refinements enforces that only materials can be refined:

```
⊢ τ   ✔️REFINE     ⊢ τ material     ⊢ r ✔️REFINE
---------------------------------------------- (SepRefMaterial)
⊢ τ r ✔️REFINE

------------------------ (SepRefBase)
⊢ ⊤, ⊥, n, x.t ✔️REFINE
```

## Properties
Lemma: exposure preserves separation, downcasting preserves separation etc:
```
⊢ Γ ✔️SEP   ⊢ τ  ✔️SEP   Γ ⊢ τ ↑ τ'
--------------------------------- (lemma Exposure__Separation)
          ⊢ τ' ✔️SEP
```
