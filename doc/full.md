
# Grammar

Variables:
  x... value variables
  t... type variables

Variance declaration:
  B := `<=` | `>=` | `=`

Types:
  beta := `⊤` | `⊥` | n |  e.t
    (base types)
  τ := beta r
  e := x | ...


Type members:
  member := `type` t B τ

Anonymous refinements:
  r := { member... }

Type declarations:
  D0 := `name` n { x => member... }
  D := D0...

Subtyping declarations:
  S := `subtype` n r <: n'

# Helpers

## Expansion

Judgment form for single-step unfolding of types `Γ ⊢_{this} τ => τ'`:  under environment Γ with self-object `this`, type `τ` evaluates to `τ'`.
Whenever we want to look inside a named definition `name n { x => ms }`, we need to know what to instantiate `this` as.
```
        name n { x => ms[x] }
  ------------------------------------- (ExpandName)
  Γ ⊢_{this} n r => n (ms[x := this] ++ r)
```

Expansion can do nothing:
```
  ------------------------------------- (ExpandId)
  Γ ⊢_{this} τ => τ

```
Expansion should really be equivalent, so `Γ ⊢ₓ τ => τ'` should imply `Γ ⊢ₓ τ <: τ' ∧ Γ ⊢ₓ τ' <: τ`

## Exposure
Nieto 2017

Exposure simplifies a path-dependent type to a non-path supertype.
Exposure `Γ ⊢ τ ↑ τ'` (up-arrow should be fat-arrow).

Interesting cases are paths:

```
x: τ ∈ Γ     Γ ⊢ τ ↑ τ'      Γ ⊢ₓ τ' => β { ...;type t <=/= τ'';... }     Γ ⊢ τ'' ↑ τ'''
---------------------------------------------------------------------------------------- (XPathRefine)
Γ ⊢ x.t ↑ τ''

x: τ ∈ Γ  Γ ⊢   τ ↑ ⊥
--------------------- (XPath⊥)
          Γ ⊢ x.t ↑ ⊥
```

Otherwise, identity:
```
τ not path
---------- (XId)
Γ ⊢ τ ↑ τ
```

Exposure should satisfy `Γ ⊢ τ ↑ τ'` implies `Γ ⊢ τ <: τ'`.

## Upcast

Upcast `Γ ⊢ τ ↑+ τ'`
for paths, expose until we get a member we can look up, but unlike exposure, don't recursively expose the member's type
```
Γ           ⊢ τ   ↑ β { ...;type t <=/= τ';... }
------------------------------------------------ (UCMember)
Γ, x: τ, Γ' ⊢ x.t ↑+ τ'

Γ           ⊢   τ ↑  ⊥
---------------------- (UC⊥)
Γ, x: τ, Γ' ⊢ x.t ↑+ ⊥

                ...if no other rules apply
--------------------- (UC⊤)
Γ ⊢ x.t ↑+ ⊤

τ not path
---------- (UCId)
Γ ⊢ τ ↑+ τ
```

## Downcast

Downcast `Γ ⊢ τ ↑- τ'`
```
Γ           ⊢ τ   ↑ β { ...;type t >=/= τ';... }
------------------------------------------------ (DCMember)
Γ, x: τ, Γ' ⊢ x.t ↑- τ'

Γ           ⊢   τ ↑  ⊥
---------------------- (DC⊤)
Γ, x: τ, Γ' ⊢ x.t ↑- ⊤

                ...if no other rules apply
--------------------- (DC⊥)
Γ ⊢ x.t ↑- ⊥

τ not path
---------- (DCId)
Γ ⊢ τ ↑- τ
```


# Subtyping

Judgment form for type subtyping, `Γ ⊢ τ <: τ'`, uses auxiliary judgment forms `Γ ⊢_{this} τ <: τ'` and `Γ ⊢ r <: r'`.

The type subtyping judgment requires the self-object because the types in the named type definition may refer to their `this` object, but anonymous refinements do not.
We want to be able to unfold named definitions `name n { this => d... }` into anonymous refinements `n { d... }`, which means that we need to be able to refer to `this` in the anonymous refinement.
It's important to be able to unfold a named definition before changing the name to a supertype: for example, if there is a declared subtyping `OrderedSet {} <: Set`
```
  name Set { this =>
    type E   <= ⊤ }
  name OrderedSet { this =>
    type E   <= ⊤;
    type Ord  <= Ord  { type E >= this.E };
    type Repr <= Tree { type E <= this.E } }
  subtype OrderedSet {} <: Set
```
We'd expect to be able to prove that `OrderedSet {} <: Set { type Repr <= Tree }`, which requires unfolding the named definition of OrderedSet to at least `OrderedSet { type Repr <= Tree { type E <= ????.E } }` before applying the explicit named supertype rule -- but we need to know how to refer to `this`.

This extra information isn't necessary in Decidable Wyvern's Wyv_core because all refinements have explicit self binders. It doesn't show up in the Nominal Wyvern thesis because types are only unfolded on paths `p.t`, which makes it quite weak. Nominal Wyvern can't show simple unfoldings such as `OrderedSet <: OrderedSet { type Repr <= Tree }`.

## Top-level type subtyping
```
  Γ, x: τ ⊢ₓ τ <: τ'
  ------------------------------ (Sub)
  Γ       ⊢  τ <: τ'
```

## Core rules
```
  ------------------- (Sub⊤)
  Γ ⊢ₓ τ <: ⊤

  ------------------- (Sub⊥)
  Γ ⊢ₓ ⊥ <: τ

  Γ ⊢    r <:   r'
  -------------------- (SubNameRefine)
  Γ ⊢ₓ n r <: n r'

  n r' <: n' \in S     Γ ⊢ r <: r'     Γ ⊢ₓ n' r <: n'' r''
  --------------------------------------------------------- (SubNameUp)
  Γ ⊢ₓ n r <: n'' r''

  Γ ⊢ₐ     r <:     r'
  ------------------------ (SubVarRefine)
  Γ ⊢ₐ x.t r <: x.t r'
```

## Member lookup rules
```
  Γ ⊢ x.t ↑+ τ     Γ ⊢ₐ τ <: τ'
  ----------------------------------------------------- (SubMemberLower)
  Γ ⊢ₐ x.t <: τ'

  Γ ⊢ x.t ↑- τ'     Γ ⊢ₐ τ <: τ'
  ----------------------------------------------------- (SubMemberUpper)
  Γ ⊢ₐ τ <: x.t
```

## Non-deterministic expansion rules
```
  Γ ⊢ₐ n r => n r'     Γ ⊢ₐ n r' <: τ''
  ----------------------------------------------------- (SubExpandLower)
  Γ ⊢ₐ n r <: τ''

  Γ ⊢ₐ n r => n r'     Γ ⊢ₐ τ <: n r'
  ----------------------------------------------------- (SubExpandUpper)
  Γ ⊢ₐ τ <: n r

```

## Auxiliary rules
```
  -------------------- (SubRefNil)
  Γ ⊢   r <: []

  type t = τ ∈ r     Γ ⊢ τ <:,:> τ'    Γ ⊢ r <: r'
  ---------------------------------------------------------------- (SubRefConsEq)
  Γ ⊢ r <: type t = τ', r'

  type t <= τ ∈ r     Γ ⊢ τ <: τ'    Γ ⊢ r <: r'
  ---------------------------------------------------------------- (SubRefConsLe)
  Γ ⊢ r  <: type t <= τ', r'

  type t >= τ ∈ r     Γ ⊢ τ' <: τ    Γ ⊢ r <: r'
  ---------------------------------------------------------------- (SubRefConsGe)
  Γ ⊢ r  <: type t >= τ', r'
```

