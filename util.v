From MetaCoq.Template Require Import All.

From MetaCoq Require Import All.
Require Import String List.
(* Local Open Scope string. *)
Import ListNotations Nat.
Import MCMonadNotation.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.PCUIC Require Import PCUICToTemplate.

Definition relevant_binder (n:name) :=
    {|
    binder_name := n;
    binder_relevance := Relevant
    |}.
Definition rAnon := relevant_binder nAnon.
Definition rName n := relevant_binder (nNamed n).
(* generates a list (n-1), ..., 0 *)
Fixpoint mkNums (n:nat) :=
    match n with 
    | O => []
    | S m => [m] ++ mkNums m
    end.
(* generates a list tRel (n-1), ..., tRel 0 *)
Fixpoint mkRels (n:nat) := map tRel (mkNums n).
Fixpoint mkAstRels (n:nat) := map Ast.tRel (mkNums n).

Definition hole := tEvar fresh_evar_id [].
Variable (TODO: forall {T}, T).
Definition AstPlaceholder := Ast.mkApp <% @TODO %> (Ast.hole).
Definition placeholder := TemplateToPCUIC.trans [] AstPlaceholder.