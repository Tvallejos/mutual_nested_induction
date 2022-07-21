(**
Provides commonly needed auxiliary definitions
*)
From MetaCoq.Template Require Import All.

From MetaCoq Require Import All.
Require Import String List.
Import ListNotations Nat.
Import MCMonadNotation.
Import IfNotations.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.PCUIC Require Import PCUICToTemplate.

(* quick way to handle new naming with relevance *)
Definition relevant_binder (n:name) :=
    {|
    binder_name := n;
    binder_relevance := Relevant
    |}.
Definition rAnon := relevant_binder nAnon.
Definition rName n := relevant_binder (nNamed n).

Definition extendName prefix (n:name) suffix :=
    match n with 
    | nAnon => nAnon
    | nNamed id => nNamed (prefix^id^suffix)
    end.
Definition extendAname prefix n suffix:= 
    map_binder_annot (fun n => extendName prefix n suffix) n.

(* generates a list (n-1), ..., 0 *)
Fixpoint mkNums (n:nat) :=
    match n with 
    | O => []
    | S m => [m] ++ mkNums m
    end.
(* generates a list tRel (n-1), ..., tRel 0 *)
(* useful to apply a bunch of arguments quantified with binders directly in front *)
Definition mkRels (n:nat) := map tRel (mkNums n).
Definition mkAstRels (n:nat) := map Ast.tRel (mkNums n).

(* hole like underscores to be inferred
  only work in limited cirumstances
  a way that works is to compute the type
  and use holes in the body which is casted to have the correct type
  but then holes can not be used inside the type

  some tricks are possible: for instance 
  when creating lambdas (for instance with eta_expansion) that
  are sure to be instanciated using beta reduction, one
  can use dummy values in the lambdas and eagerly (with mkEagerApp)
*)
Definition hole := tEvar fresh_evar_id [].

(* can be quoted as more powerful hole (coq does not need to fill it in)
    only for testing/debugging purposes
 *)
(* Variable (TODO: forall {T}, T).
Definition AstPlaceholder := Ast.mkApp <% @TODO %> (Ast.hole).
Definition placeholder := TemplateToPCUIC.trans [] AstPlaceholder. *)



(*
n = destination
k = local binder count

works like subst: replaces binders behind n with an instance from s
if s is large enough otherwise, reduce the binder to simulate instantiation
*)
Fixpoint local_subst_ (s:list term) (n:nat) (k:nat) (t:term) := 
  match t with
  | tRel m =>
      (* difference: correct distance is dest (n)+local (k) *)
	  if k+n <=? m
      then
        (* difference: only lift over local binders *)
        if nth_error s (m - k-n) is Some b then lift0 k b else tRel (m - #|s|)
      else tRel m
  | tEvar ev args => tEvar ev (map (local_subst_ s n k) args)
  | tProd na A B => tProd na (local_subst_ s n k A) (local_subst_ s n (S k) B)
  | tLambda na T M => tLambda na (local_subst_ s n k T) (local_subst_ s n (S k) M)
  | tLetIn na b ty b' =>
      tLetIn na (local_subst_ s n k b) (local_subst_ s n k ty) (local_subst_ s n (S k) b')
  | tApp u0 v => tApp (local_subst_ s n k u0) (local_subst_ s n k v)
  | tCase ind p c brs =>
      let p' := map_predicate_k id (local_subst_ s n) k p in
      let brs' := map_branches_k (local_subst_ s n) id k brs in
      tCase ind p' (local_subst_ s n k c) brs'
  | tProj p c => tProj p (local_subst_ s n k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (local_subst_ s n k) (local_subst_ s n k')) mfix in
      tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (local_subst_ s n k) (local_subst_ s n k')) mfix in
      tCoFix mfix' idx
  | _ => t
  end.

Definition local_subst s n := local_subst_ s n 0.



(*
performs beta reduction if directly applicable
otherwise, introduce application
*)
(* TODO: there once was a function doing this already (was it mkApp in a previous version?) *)
Definition mkEagerApp (a:term) (b:term) : term :=
    match a with 
    (* we completely ignore the type of the lambda as we might eliminate an error or at least do not introduce one *)
    | tLambda na _ body =>
        body {0:=b}
    | _ => tApp a b 
    end.

Fixpoint mkEagerApps (t:term) (us:list term) : term :=
    match us with
    | [] => t
    | u::ur => mkEagerApps (mkEagerApp t u) ur
    end.