
# Grammar

Variables:
  x... value variables
  t... type variables

Types:
  tau := `TOP` | `BOT` | n r | tau.t | x

Type members:
  member := `type` t phi
  PHI    := `<=` | `>=`
            (variance-modes)
  phi    := `<=` tau | `>=` tau | tau
            (variance-types)

Anonymous refinements:
  r := { member;... }

Type declarations:
  D0 := `name` n { x => member;... }
  D := D0...

Subtyping declarations:
  S := `subtype` n r <: n'

  gamma := x : tau;...

# Helpers

## Modal stepping

Judgment form for single-step evaluation of types `gamma |- tau => phi`:
  under environment gamma, pure type tau evaluates to variance-type phi
```

        name n { x => ms[x] }
  ------------------------------------- (StepName)
  gamma |- n r => n (ms[x := n r] ++ r)

  ---------------------- (StepVar)
  gamma |- x => gamma(x)

  gamma |- tau   => tau'
  ---------------------------- (StepSelectSPure)
  gamma |- tau.t => tau'.t

  gamma |- tau   => PHI tau'
  ---------------------------- (StepSelectSPhi)
  gamma |- tau.t => PHI tau'.t

  type t phi \in r
  ---------------------------- (StepSelect0)
  gamma |- (n r).t => phi
```

# Subtyping

Judgment form for type subtyping `gamma |-_PHI tau <: tau'`, uses auxiliary judgment form `gamma |- phi <: phi'` and `gamma |- r <: r'`

## Core rules
```
  ------------------- (SubTop)
  gamma |-_PHI tau <: TOP

  ------------------- (SubBot)
  gamma |-_PHI BOT <: tau

  gamma |-_PHI   r <:   r'
  -------------------- (SubNameEq)
  gamma |-_PHI n r <: n r'

  n r' <: n' \in S     gamma |-_PHI r <: r'     gamma |-_PHI n' r <: n'' r''
  ---------------------------------------------------------------- (SubNameUp)
  gamma |-_PHI n r <: n'' r''
```

## Non-deterministic rules
```
  gamma |- tau => PHI tau'     gamma |-_PHI tau' <: tau''
  ----------------------------------------------------- (SubStepLeft)
  gamma |-_PHI tau <: tau''

  gamma |- tau' => PHI tau''     gamma |-_PHI tau <: tau''
  ----------------------------------------------------- (SubStepRight)
  gamma |-_PHI tau <: tau'
```

## Auxiliary phi rules
```
  gamma |-_(<=)     tau  <:     tau'
  ------------------------------ (SubPhiVariant)
  gamma |- (<= tau) <: (<= tau')

  gamma |-_(>=)     tau' <:     tau
  ------------------------------ (SubPhiContra)
  gamma |- (>= tau) <: (>= tau')

  gamma |-(...)     tau  <:&:>  tau'
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
