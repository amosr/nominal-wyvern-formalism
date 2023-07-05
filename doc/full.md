
# Grammar

Variables:
  x... value variables
  t... type variables

Variance declaration:
  R := `<=` | `>=` | `=`

Types:
  tau := `TOP` | `BOT` | n r |  tau.t | x
-- separate `x` and `tau.t` so substitution is total / deterministic


Type members:
  member := `type` t R tau

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

Judgment form for single-step evaluation of types `gamma |- tau =>_{hand} tau'`:
  under environment gamma, on hand side of subtyping (left or right), type tau evaluates to tau'
```

        name n { x => ms[x] }
  ------------------------------------- (StepName)
  gamma |- n r => n (ms[x := n r] ++ r)


  ---------------------- (StepVar)
  gamma |- x => gamma(x)

  gamma |- tau   => tau'
  ---------------------------- (StepSelectS)
  gamma |- tau.t => tau'.t


  tau' = coerce r[t] h
  ---------------------------- (StepSelect0)
  gamma |- (n r).t =>_h tau'

```


# Subtyping

Judgment form for type subtyping `gamma |- tau <: tau'`, uses auxiliary judgment form `gamma |- r <: r'`

## Core rules
```
  ------------------- (SubTop)
  gamma |- tau <: TOP

  ------------------- (SubBot)
  gamma |- BOT <: tau

  gamma |-   r <:   r'
  -------------------- (SubNameEq)
  gamma |- n r <: n r'

  n r' <: n' \in S     gamma |- r <: r'     gamma |- n' r <: n'' r''
  ---------------------------------------------------------------- (SubNameUp)
  gamma |- n r <: n'' r''
```

## Non-deterministic rules
```
  gamma |- tau =>_{LHS} tau'     gamma |- tau' <: tau''
  ----------------------------------------------------- (SubStepLeft)
  gamma |- tau <: tau''

  gamma |- tau' =>_{RHS} tau''     gamma |- tau <: tau''
  ----------------------------------------------------- (SubStepRight)
  gamma |- tau <: tau'
```

## Auxiliary rules
```
  -------------------- (SubRefNil)
  gamma |-   [] <:   []

  type t = tau' \in r'     gamma |- tau <:,:> tau'    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsEq)
  gamma |- type t = tau, r  <: r'

  type t <= tau' \in r'     gamma |- tau <: tau'    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsLe)
  gamma |- type t <= tau, r  <: r'

  type t >= tau' \in r'     gamma |- tau' <: tau    gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsGe)
  gamma |- type t >= tau, r  <: r'

  type t \not\in r'                                gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsMissing)
  gamma |- type t ... , r  <: r'
```


## Fixup rules
We need some extra rules for reflexivity.
SubSelectRefl is very strong.

```
  ------------------- (SubVarRefl)
  gamma |- x <: x

  ----------------------- (SubSelectRefl)
  gamma |- tau.t <: tau.t
```

Transitivity?




# Problems

Applying same refinement to both sides should not affect subtyping. Expect this to be true:
```
tau                  <:  tau'
---------------------------------------------
tau { type t = rho } <: tau' { type t = rho }
```

But the same doesn't hold inside a member selection:
```
tau.t                    <:  tau'.t
-----------------------------------------------------
(tau { type t' = rho }).t <: (tau' { type t' = rho }).t
```
