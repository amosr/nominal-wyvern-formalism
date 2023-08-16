# Structural decidable subtyping

Comparison of Decidable Wyvern (Wyv_{self} in POPL2019) and Nominal Wyvern.

## Similarities:

### Shapes / acyclic restriction on graphs
Both systems have basically the same restriction on cycles.

### Syntactic separation between materials and shapes
Both have syntactic restrictions on where shapes can be used.
Decidable Wyvern defines these restrictions in terms of mutually recursive grammars τ, σ (shapes) and μ, δ (materials).
Nominal Wyvern defines similar restrictions as a separate syntactic check.
Billy's thesis (3.4) says that the separate syntactic check is simpler than baking them into the grammar, but they're not formally defined in Billy's thesis or the paper submission (just prose descriptions).

It seems to me to just be a different way to present what are basically the same restrictions, and I don't see how it's fundamentally simpler.

### No recursion / self-binding in refinements

Nominal Wyvern does not support self-binding in refinements at all: all refinements are of the form  `τ { σ... }` rather than `τ { z => σ... }`.
In Nominal Wyvern, only class definitions have self-binding.

Decidable Wyvern (Wyv_{self}) disallows self-binding on material refinements, but allows them on mixed types: `μ { δ... }` and `τ { z => σ... }`.

There is a slight difference in the details because Decidable Wyvern doesn't have type definitions, but the concept is basically the same.

### No trivial refinements
In both Nominal Wyvern and Decidable Wyvern, the check for a refined type `τ { r } <: τ { r' }` checks that each member of `r'` is included in the refinement `r`, but it doesn't look in `τ`.
Given a definition something like `name Set = { type Repr = Vector }`, we can't show trivial refinements such as `Set <: Set { type Repr = Vector }`.

I originally thought this worked in Decidable Wyvern because of the S-Extend and E-Refine rules, but it's kind of subtle. We could encode the named type as a type member equality:
```DW
set: { self => type Set = Top { type Repr = Vector } }
```
If we try to check a similar example then we can apply S-Extend and E-Refine to unfold the left-hand-side:
```DW
-----------------------------------------
Top { type Repr = Vector } <: set.Set { type Repr = Vector }
----------------------------------------- (S-Extend, E-Refine)
set.Set <: set.Set { type Repr = Vector }
```
Intuitively, it feels like we should be able to apply S-Lower to unfold the definition of `set.Set` on the right-hand-side and end up with `(Top { type Repr = Vector }) { type Repr = Vector }`, but the S-Lower rule doesn't allow refinements on the type member, so we're stuck.

## Differences:

### Decidable Wyvern supports nominal type members
Decidable Wyvern has nominal type members `L ≼ τ`.
There are two extension rules for this: E-Mat and E-Shape.

Nominal Wyvern does not need these.
These rules don't seem too complicated - I don't know whether we could claim that Nominal Wyvern is that much simpler without them.

### Nominal Wyvern does not have quantifiers or methods in type refinements

Decidable Wyvern has explicit universal quantifiers as a type, and they're allowed to appear anywhere types can appear, including in refinements.
Having quantifiers in types means that Decidable Wyvern needs to restrict contravariance somehow in its S-All rule.

Nominal Wyvern does not have universal quantifiers, except those that appear inside method definitions.
These method definitions cannot appear in refinements or in types, and only in named type definitions.

By only allowing quantifiers in type definitions, and not in types, it means that Nominal Wyvern's contravariant SS-Def rule is only ever called at the top level, and cannot be called recursively within itself.
It would probably be clearer to restructure the subtyping judgment so that the SS-Def rule isn't part of the recursive subtyping judgment.

The restricted occurrence of quantifiers allows Nominal Wyvern to use full contravariance, but at the cost of limited expressivity.
