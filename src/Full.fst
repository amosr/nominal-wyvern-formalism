(* Formalising subtyping for Nominal Wyvern *)
module Full

module M = Maps
module I = Indices

(* abstract names for global type declarations *)
assume type global: Prims.eqtype
(* abstract names for type members *)
assume type type_member: Prims.eqtype

(* TODO: Capture-avoiding substitution

  In Nominal Wyvern, anonymous refinements do not have access to the `this`
  variable, which means that a type definition can only have one `this` binder
  in scope. Ignore methods / dependent function types for now, so we can also
  ignore capture-avoiding substitution.

  Methods will need capture-avoiding substitution though:
  > name K1 { this =>
  >   def method(param: K2): this.t
  > }
  Substitute K1[this := param] requires renaming method binder.

*)

type bound = | LE | GE | EQ

type ty =
 (* initial type: `Top` *)
 | TTop : ty
 (* terminal type: `Bottom` *)
 | TBot : ty
 (* global type `n` *)
 // TODO split out refinement to base_ty / ref_ty
 | TGlobal : (n: global) -> (r: refinement) -> ty
 (* path-dependent type: `x.t` *)
 | TSelect : (t: ty) -> (m: type_member) -> ty
 | TVar : (x: I.var) -> ty
 (* Note: TSelectVar:
    XXX: TSelect and TVar were originally one constructor TSelectVar `x.t`.
    however, (hereditary) substitution is non-terminating if it needs to normalise to `x.t` form:
    > x.t[x := {x' => type t = x'.t }]
    = {x' => type t = x'.t}.t
    = x'.t[x' := {x'' => type t = x''.t}]
    = ...

    Decidable Wyvern paper disallows recursion in refinements, so the above `{x' => type t = x'.t}`
    could not be written as an anonymous refinement, but we still need to
    substitute in the body to normalise to a variable

    > name n { x => type t = x.t }
    > x.t[x := n]
    = n.t         (not grammatically valid)
    = { x => type t = x.t }.t
    = ...

    A second problem with substitution on TSelectVar is that substitution has
    to commit to a particular type too early. For example:
    > x.t[x:= {type t <= tau}] <: x.t[x:= {type t <= tau}]
    what should the two occurrences simplify to: tau, Top or Bot? it depends on the context:
    the LHS can simplify to tau, but the RHS has to simplify to Bot.
    Eg if we always simplified to tau, we'd be able to prove:
    > x : { type t <= tau }; y: { type t <= tau } |- x.t <: y.t
    which is not true because x and y refer to totally different types
    Upper bounds also have to simplify differently depending on the context:
    > x : { type t >= tau }; y: { type t <= tau } |- x.t <: y.t
  *)
and member =
 | Member : (b: bound) -> (t: ty) -> member
and refinement =
  (* refinement with no local `this` in scope *)
  M.partial type_member member


type gamma = I.gamma ty


(* a single class declaration.
 this looks very similar to `refinement`, but each member is checked in a
 context with a new `this` variable referring to the current class *)
type class_decl =
  | Decl: (ds: M.partial type_member member) -> class_decl

(* class declaration environment (\Delta) *)
type class_decls = global -> class_decl

// noeq
// type subtype_decl = {
//   // lhs_global: global;
//   lhs_refine: refinement;
//   rhs_global: global;
// }
// 
// type subtype_decls = global -> list subtype_decl

(* set/predicate encoding of declared subtype relations: easier to use in subtyping rules *)
type subtype_decls = global -> refinement -> global -> bool

noeq
type program = {
  classes: class_decls;
  subtypes: subtype_decls;
}


(* Simple substitution. We can avoid worrying about capture and lifting for now
  because we don't have dependent functions in types *)
let rec subst_ty (t: ty) (x: I.var) (p: ty): Tot ty (decreases t) =
  match t with
  | TTop | TBot  -> t
  | TGlobal n  r -> TGlobal n (subst_refinement r x p)
  | TSelect t' m -> TSelect (subst_ty t' x p) m
  | TVar    x'   -> if x = x' then p else t

and subst_refinement (r: refinement) (x: I.var) (p: ty): Tot refinement (decreases r) =
  match r with
  | [] -> []
  | (m, md) :: r' ->
    // nested pattern match required for termination proof?
    match md with
    | Member b t ->
      (m, Member b (subst_ty t x p)) :: subst_refinement r' x p



(* subtyping direction, or side of an equation (LHS <: RHS) *)
type hand = | LHS | RHS

(* interpret a member declaration as an upper or lower bound.
  coerce _ LHS interprets as upper bound, RHS as lower bound.
  for example, consider the typing rule:

      g |- coerce t.x LHS <: tau'
    ---------------------------------------------
      g |-        t.x     <: tau'

  here, t.x is used as the lower bound, so we want to get the 'largest' type
  that t.x could be. if `t.x` is defined as `type t <= tau` then we use tau.
  if it is defined as `type t >= tau` then we approximate tau's upper bound as top.
 *)

let coerce (m: member) (h: hand): ty =
  match m, h with
  | Member EQ t, _ -> t
  | Member LE t, LHS -> t
  // TODO: could make this more precise by unfolding definitions from refinement
  | Member GE t, LHS -> TTop
  | Member LE t, RHS -> TBot
  | Member GE t, RHS -> t


assume val p: program

let unfold_global (t: ty { TGlobal? t }): refinement =
  let Decl r' = p.classes (TGlobal?.n t) in
  subst_refinement r' 0 t

(* simplify step / unfold for types:
  step g h t t' `g |- t ==>_h t'`
 *)
type step (g: gamma) (h: hand): ty -> ty -> Type =
 | StepName:
   (n: global) ->
   (r: refinement) ->
   step g h
    (TGlobal n                                         r)
    (TGlobal n (M.mergeR (unfold_global (TGlobal n r)) r))

 | StepVar:
   (x: I.var) ->
   (t: ty { I.get g x == (Some t) }) ->
   step g h (TVar x) t

 | StepSelectS:
   (t: ty) ->
   (t': ty) ->
   (m: type_member) ->
   (s0: step g h t t') ->
   step g h
    (TSelect t  m)
    (TSelect t' m)

 | StepSelect0:
   (n: global) ->
   (r: refinement) ->
   (m: type_member) ->
   (m': member { M.get r m == Some m' }) ->
   step g h
    (TSelect (TGlobal n r)  m)
    (coerce m' h)

 (* Backtracking: always Top: these look a lot like the Uc-Top and Dc-Bot rules in strong D<: *)
//  | StepTop:
//    (t: ty) ->
//    step g LHS t TTop
//  | StepBot:
//    (t: ty) ->
//    step g RHS t TBot

type sub (g: gamma): ty -> ty -> Type =
 | SubTop:
   (t: ty) ->
   sub g t TTop
 | SubBot:
   (t: ty) ->
   sub g TBot t

 | SubVarRefl:
   (x: I.var) ->
   sub g (TVar x) (TVar x)
 (*
  XXX: we need fairly strong axioms for reflexivity:
  > tau.m <: tau.m

  this is required because variable lookups are asymmetric. for example:
  > x: n { type m <= tau } |- x.m <: x.m
  if we fully step the left-hand side, it becomes tau:
  > ... |- n { type m <= tau }.m <: x.m (SubStepLeft, StepSelectS, StepVar)
  > ... |-               tau     <: x.m (SubStepLeft, StepSelect0, coerce.LE.LHS)
  but the right-hand side becomes TBot:
  > ... |-               tau     <: { type m <= tau }.m (SubStepRight, StepSelectS, StepVar)
  > ... |-               tau     <: TBot (SubStepRight, StepSelect0, coerce.LE.RHS)

  but we cannot prove `tau <: TBot`, so if we want reflexivity we need an axiom
  to apply before stepping.
 *)
 | SubSelectRefl:
   (t: ty) ->
   (m: type_member) ->
   sub g (TSelect t m) (TSelect t m)

 | SubStepLeft:
   (t: ty) -> (t': ty) -> (t'': ty) ->
   step g LHS t t' ->
   sub g t' t'' ->
   sub g t t''
 | SubStepRight:
   (t: ty) -> (t': ty) -> (t'': ty) ->
   step g RHS t' t'' ->
   sub g t t'' ->
   sub g t t'

 | SubNameEq:
   (n: global) ->
   (r: refinement) ->
   (r': refinement) ->
   sub_refinement g r r' -> // not gamma (TGlobal n r :: g)
   sub g (TGlobal n r) (TGlobal n r')
 | SubNameUp:
   (n: global) ->
   (r: refinement) ->
   (n': global) ->
   (n'': global) ->
   (r'': refinement) ->
   // (n rd <: n') \in \Sigma
   (rd: refinement { p.subtypes n rd n' }) ->
   sub_refinement g r rd -> // not gamma (TGlobal n r :: g)
   sub g (TGlobal n' r) (TGlobal n'' r'') ->
   sub g (TGlobal n  r) (TGlobal n'' r'')

and sub_refinement (g: gamma): refinement -> refinement -> Type =
 | SubRefNil:
   (r': refinement) ->
   sub_refinement g [] r'

 | SubRefConsLE:
   (m: type_member) ->
   (t: ty) ->
   (r: refinement) ->
   (r': refinement) ->
   (t': ty { M.get r' m == Some (Member LE t') }) ->
   sub g t t' ->
   sub_refinement g r r' ->
   sub_refinement g ((m, Member LE t) :: r) r'

 | SubRefConsEQ:
   (m: type_member) ->
   (t: ty) ->
   (r: refinement) ->
   (r': refinement) ->
   (t': ty { M.get r' m == Some (Member EQ t') }) ->
   sub g t t' ->
   sub g t' t ->
   sub_refinement g r r' ->
   sub_refinement g ((m, Member EQ t) :: r) r'

 | SubRefConsGE:
   (m: type_member) ->
   (t: ty) ->
   (r: refinement) ->
   (r': refinement) ->
   (t': ty { M.get r' m == Some (Member GE t') }) ->
   sub g t' t ->
   sub_refinement g r r' ->
   sub_refinement g ((m, Member GE t) :: r) r'

 | SubRefConsNone:
   (b: bound) ->
   (m: type_member) ->
   (t: ty) ->
   (r: refinement) ->
   (r': refinement { M.get r' m == None }) ->
   sub_refinement g r r' ->
   sub_refinement g ((m, Member b t) :: r) r'


let lemma_step_not_select_same
  (g: gamma)
  (t: ty  { not (TSelect? t )})
  (tl: ty)
  (sl: step g LHS t tl)
  (tr: ty)
  (sr: step g RHS t tr):
  Lemma (tl == tr) =
  ()

let rec lemma_sub_refl (g: gamma) (t: ty):
  Tot (sub g t t) (decreases t) =
  match t with
  | TTop -> SubTop _
  | TBot -> SubBot _
  | TGlobal n r -> SubNameEq n r r (lemma_sub_refinement_refl _ r)
  | TSelect t m -> SubSelectRefl t m
  | TVar x -> SubVarRefl x
and lemma_sub_refinement_refl (g: gamma) (r: refinement):
  Tot (sub_refinement g r r) (decreases r) =
  // TODO refl for refinement needs to be stronger:
  // (forall x in r, M.get x.k r' == x.v) -> sub_refinement g r r'
  // for partial (forall x in r, M.get x.k r == x.v)
  // also requires no dups
  admit ()

// trans


// inversion:
// let lemma_inversion_top
//   (g: gamma)
//   (t: ty)
//   (s: sub TTop t):
//   step_many LHS t TTop
// and bot

// steps are good
// let lemma_one_step_ok:
//   (g: gamma)
//   (t tl tr: ty)
//   (sl: step LHS t tl)
//   (sl: step RHS t tr):
//   sub tr t /\ sub t tr

// define validity