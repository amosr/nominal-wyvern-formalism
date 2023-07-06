
# Grammar

Variables:
  x... value variables
  t... type variables

Variance declaration:
  B := `<=` | `>=` | `=`

Types:
  beta := `TOP` | `BOT` | n |  e.t
    (base types)
  tau := beta r
  e := x | ...


Type members:
  member := `type` t B tau

Anonymous refinements:
  r := { member... }

Type declarations:
  D0 := `name` n { x => member... }
  D := D0...

Subtyping declarations:
  S := `subtype` n r <: n'

# Helpers

## Coerce
Left or right hand side of subtyping relation:
```
  hand := `LHS` | `RHS`
```

Coercion interprets a member as a type. This isn't as simple as it looks, because it depends what side of the subtyping relation you're looking at.
For example, a relation with variant on left and contravariant on right should not hold: `type t >= tau \not<: type t <= tau`.
To achieve this, a constraint `type t <= tau` is interpreted as `tau` on the left-hand side, but on the right-hand side it reads as bottom.
This up-casting of the left-hand-side to top, and down-casting the right-hand-side to bottom, is comparable to the Uc-Top and Dc-Bot rules in kernel `D<:`.

```
  coerce : member -> hand -> tau
  -- Invariant members
  coerce (type t  = tau) _   = tau

  -- Variant members
  coerce (type t <= tau) LHS = tau
  coerce (type t <= tau) RHS = BOT

  -- Contravariant members
  coerce (type t >= tau) LHS = TOP
  coerce (type t >= tau) RHS = tau
```

## Stepping

Judgment form for single-step evaluation of types `gamma |-^{hand}_{this} tau => tau'`:  under environment gamma with self-object `this`, on hand side of subtyping (left or right), type `tau` evaluates to `tau'`.
Whenever we want to look inside a named definition `name n { x => ms }`, we need to know what to instantiate `this` as.
```

        name n { x => ms[x] }
  ------------------------------------- (StepName)
  gamma |-^{hand}_{this} n {} => n ms[x := this]

  ------------------------------------------------------ (StepSelect)
  gamma, x: tau, gamma' |-^{hand}_{this} x.t {} => coerce tau(t) hand

  gamma, y : tau |-^{hand}_y tau_y => tau_y'    gamma, y : tau_y', gamma' |-^{hand}_{this} tau => tau'
  -------------------------------------------------------------------------------------- (StepEnv)
  gamma, y : tau, gamma' |-^{hand}_{this} tau => tau'

  gamma |-^{hand}_{this} beta   => beta' r'
  ------------------------------------------------ (StepRefine)
  gamma |-^{hand}_{this} beta r => beta' (r' ++ r)
```

If `gamma |-_x tau =>_{hand} tau'` and `gamma |- x: tau`, then `gamma |- x: tau'`???

# Subtyping

Judgment form for type subtyping, `gamma |- tau <: tau'`, uses auxiliary judgment forms `gamma |-_{this} tau <: tau'` and `gamma |- r <: r'`.

The type subtyping judgment requires the self-object because the types in the named type definition may refer to their `this` object, but anonymous refinements do not.
We want to be able to unfold named definitions `name n { this => d... }` into anonymous refinements `n { d... }`, which means that we need to be able to refer to `this` in the anonymous refinement.
It's important to be able to unfold a named definition before changing the name to a supertype: for example, if there is a declared subtyping `ArrayList r <: List`
```
  name Set { this =>
    type E   <= Top }
  name OrderedSet { this =>
    type E   <= Top;
    type Ord  <= Ord  { type E >= this.E };
    type Repr <= Tree { type E <= this.E } }
  subtype OrderedSet <: Set
```
We'd expect to be able to prove that `OrderedSet <: Set { type Repr <= Tree }`, which requires unfolding the named definition of OrderedSet to at least `OrderedSet { type Repr <= Tree { type E <= ????.E } }` before applying the explicit named supertype rule -- but we need to know how to refer to `this`.

This extra information isn't necessary in Decidable Wyvern's Wyv_core because all refinements have explicit self binders. It doesn't show up in the Nominal Wyvern thesis because types are only unfolded on paths `p.t`, which makes it quite weak. Nominal Wyvern can't show simple unfoldings such as `OrderedSet <: OrderedSet { type Repr <= Tree }`.

## Top-level type subtyping
```
  gamma, x: tau |-_x tau <: tau'
  ------------------------------ (Sub)
  gamma         |-   tau <: tau'
```

## Core rules
```
  ------------------- (SubTop)
  gamma |-_x tau <: TOP

  ------------------- (SubBot)
  gamma |-_x BOT <: tau

  gamma |-     r <:   r'
  -------------------- (SubNameRefine)
  gamma |-_x n r <: n r'

  n r' <: n' \in S     gamma |- r <: r'     gamma |-_x n' r <: n'' r''
  ---------------------------------------------------------------- (SubNameUp)
  gamma |-_x n r <: n'' r''

  gamma |-     r <:     r'
  ------------------------ (SubVarRefine)
  gamma |- x.t r <: x.t r'
```

## Non-deterministic stepping rules
```
  gamma |-^{LHS}_x tau => tau'     gamma |-_x tau' <: tau''
  ----------------------------------------------------- (SubStepLeft)
  gamma |-_x tau <: tau''

  gamma |-^{RHS}_x tau' => tau''     gamma |-_x tau <: tau''
  ----------------------------------------------------- (SubStepRight)
  gamma |-_x tau <: tau'
```

## Auxiliary rules
```
  -------------------- (SubRefNil)
  gamma |-   [] <:   []

  type t = tau' \in r'     gamma, x: tau |-_x tau <:,:> tau'    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsEq)
  gamma |- type t = tau, r  <: r'

  type t <= tau' \in r'     gamma, x: tau |-_x tau <: tau'    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsLe)
  gamma |- type t <= tau, r  <: r'

  type t >= tau' \in r'     gamma, x: tau' |-_x tau' <: tau    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsGe)
  gamma |- type t >= tau, r  <: r'

  type t \not\in r'                                gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsMissing)
  gamma |- type t ... , r  <: r'
```

