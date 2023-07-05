
# Grammar

Variables:
  x... value variables
  t... type variables

Types:
  tau := `TOP` | `BOT` | n r | tau.t | x

Type members:
  member := `type` t phi
  phi    := `<=` tau | `>=` tau | `=` tau
            variance-type

Anonymous refinements:
  r := { member... }

Type declarations:
  D0 := `name` n { x => member... }
  D := D0...

Subtyping declarations:
  S := `subtype` n r <: n'

# Helpers

## Stepping

Judgment form for single-step evaluation of types `gamma |- tau => phi`:
  under environment gamma, type tau evaluates to variant type phi
```

        name n { x => ms[x] }
  ------------------------------------- (StepName)
  gamma |- n r => n (ms[x := n r] ++ r)


  ---------------------- (StepVar)
  gamma |- x => gamma(x)

  gamma |- tau   => tau'
  ---------------------------- (StepSelectS)
  gamma |- tau.t => tau'.t
```

```
  ---------------------------- (StepSelect0)
  gamma |- (n r).t => r(t)
```


# Subtyping

Judgment form for type subtyping `gamma |- tau <: tau'`, uses auxiliary judgment form `gamma |- phi <: phi'` and `gamma |- r <: r'`

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

## Auxiliary phi rules
```
  gamma |-     tau  <:     tau'
  ------------------------------ (SubPhiVariant)
  gamma |- (<= tau) <: (<= tau')

  gamma |-     tau' <:     tau
  ------------------------------ (SubPhiContra)
  gamma |- (>= tau) <: (>= tau')

  gamma |-     tau  <:&:>  tau'
  ------------------------------ (SubPhiInvariant)
  gamma |-  (= tau) <:  (= tau')
```

```
  -------------------- (SubRefNil)
  gamma |-   [] <:   []

  type t phi' \in r'     gamma |- phi <: phi'      gamma |- r <: r'
  ----------------------------------------------------------------- (SubRefCons)
  gamma |- type t phi, r  <: r'

  type t \not\in r'                                gamma |- r <: r'
  ---------------------------------------------------------------- (SubRefConsMissing)
  gamma |- type t phi, r  <: r'
```
