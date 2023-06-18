(* Formalising subtyping for Nominal Wyvern *)
module Nom0

(* name of global type declaration *)
assume type global
(* name of type member *)
assume type type_member
(* a name referring to a runtime object *)
assume type object

type rel = | LE

(* types *)
noeq
type ty =
 (* initial type: `Top` *)
 | TTop : ty
 (* terminal type: `Bottom` *)
 | TBot : ty
 (* refined global type `n { t = ty',... }` *)
 | TGlobal : global -> refinement -> ty
 (* type member: `p.t` or `x.t` *)
 | TMember : object -> type_member -> ty
and
 (* { t <= ty,... } *)
 refinement = type_member -> option (rel & ty)

(* higher-order abstract syntax for class declarations:

  name List { this =>
    type T <= Top
    type E <= this.E
  }

  is represented as:

  class_decl = \this t ->
    match t with
    | TM_T -> TTop
    | TM_E -> TMember this TM_T
  *)
type class_decl = object -> type_member -> ty

(* class declaration environment (\Delta) *)
type class_decls = global -> class_decl

noeq
type subtype_decl = {
  // lhs_global: global;
  lhs_refine: refinement;
  rhs_global: global;
}

type subtype_decls = global -> list subtype_decl

noeq
type program = {
  classes: class_decls;
  subtypes: subtype_decls;
}

noeq
type sem = {
//  s_ty:     ty     -> object -> prop;
  s_global: global -> object -> prop;
  s_member: object -> type_member -> ty;
}


noeq
type sem_ty (s: sem): ty -> Type =
  | SemTop:
    (forall (o: object). s.s_ty TTop o) ->
    sem_ty s TTop
  | SemGlobal:
    g: global ->
    r: refinement ->
    s.s_global g o ->
    sem_ref s r o ->
    sem_ty s o (TGlobal g r)
  | SemMember:
    o': object ->
    t: type_member ->
    sem_member o' t o ->
    sem_ty o (TMember o' t)
and
  sem_ref (r: refinement) (o: object): Type =
   | SemRef:
     (forall (t: type_member).
       match r t with
       | None -> True
       | Some (r, t') -> sem_ty o t') ->
     sem_ref r o










(* denotational semantics for subtyping:
  a type is a predicate on objects *)
type sem = object -> prop

assume val classes: class_decls
assume val subtypes: subtype_decls

(* true if object is tagged with `global` constructor *)
assume val sem_global: global -> sem

assume val sem_member: object -> type_member -> sem

noeq
type sem_ty (o: object): ty -> Type =
  | SemTop: sem_ty o TTop
  | SemGlobal:
    g: global ->
    r: refinement ->
    sem_global g o ->
    sem_ref r o ->
    sem_ty o (TGlobal g r)
  | SemMember:
    o': object ->
    t: type_member ->
    sem_member o' t o ->
    sem_ty o (TMember o' t)
and
  sem_ref (r: refinement) (o: object): Type =
   | SemRef:
     (forall (t: type_member).
       match r t with
       | None -> True
       | Some (r, t') -> sem_ty o t') ->
     sem_ref r o

let sem_class (g: global) (c: class_decl): sem = fun o ->
  sem_global g o ==>
  (forall (t: type_member) (o': object).
  (sem_member o t o' <==> sem_ty o' (c o t)))

let sem_classes (c: class_decls): sem = fun o ->
  forall (g: global). sem_class g (c g) o

let sem_subtype (g: global) (r: refinement) (g': global): sem = fun o ->
  sem_global g o ==>
  sem_ref    r o ==>
  sem_global g' o
