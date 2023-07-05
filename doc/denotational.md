Denotational semantics of subtyping relation

# Grammar

Variables:
  x... value variables
  t... type variables

Variance declaration:
  R := `<=` | `>=` | `=`

Types:
  tau := `TOP` | `BOT` | n r | e.t
  e   := x | Object

Type members:
  member := `type` t R tau

Anonymous refinements:
  r := { member... }

Type declarations:
  D0 := `name` n { x => member... }
  D := D0...

Subtyping declarations:
  S := `subtype` n r <: n'

# Denotations

  Type = Object -> Store -> Prop
  Object = { tag: n; values : Field -> Object; types : Member -> Type }
  Gamma = Index -> Type
  Store = Index -> Object

assume lifted environment Γ: Index -> Type
assume Δ: n -> D0, Σ: n r -> n'

[| tau |]
  sem_ty : tau -> Type
  sem_ty TOP = λo. True
  sem_ty BOT = λo. False

  sem_ty (n r) = λo. sem_name n o /\ sem_ref r o
  sem_ty e.t   = λo. (sem_exp e).types t o

[| exp |] σ
  sem_exp : e -> Object
  sem_exp x = σ x
  sem_exp o = o

[| n |]
  sem_name : n -> Type
  sem_name n
    | name n { this => r... } : Δ
    = λo. check_supertag n o.tag /\
          sem_ref r[this := o] o

  sem_ref : r -> Type
  sem_ref ms = λo. /\_{m : ms} sem_member m o

  sem_member : m -> Type
  sem_member (type t  = tau) = λo.                o.t <==> sem_ty tau
  sem_member (type t <= tau) = λo. ∀o'.        o.t(o') ==> sem_ty tau o'
  sem_member (type t >= tau) = λo. ∀o'. sem_ty tau o'  ==>        o.t(o')

  check_supertag n n' =
   n == n' \/
   (∃n'. n' r <: n'' : Σ /\ check_supertag n n'')

