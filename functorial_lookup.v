(**
Collects inductives from an one_inductive_body 
that is, collect all inductive types appearing inside

also generates a lookup table for functorial instances
*)
Require Import functorial.

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

Class functorial_instance (func_ind:inductive) :=
     {
         param_groups : nat;
         func_lemma : term;
     }.

Section Generation.

(* recurses under binders and collects all inductives from tInd *)
Fixpoint collect_tInd_term  (t:term) : list inductive :=
    match t with
    | tInd ind _ => [ind]
    | tApp a b
    | tProd _ a b
    | tLambda _ a b =>
        collect_tInd_term a ++ collect_tInd_term b
    | _ => []
    end.

    (* takes inductives from type and constructors *)
Definition collect_tInd (ind:one_inductive_body) : list inductive :=
    collect_tInd_term ind.(ind_type) ++
    concat (map
    (fun ctor => collect_tInd_term ctor.(cstr_type))
    ind.(ind_ctors)).


    (* looks up each inductive for a registered functorial instance
    if one is found write down param group count and functorial lemma
    into a list
     *)
Definition lookup_table (xs:list inductive) : 
    TemplateMonad (list (inductive * (nat * term))) :=
    monad_fold_left
        (fun lt ind =>
        lr <- tmInferInstance (Some lazy) (functorial_instance ind);;
        match lr with
        | my_None => ret lt
        | my_Some {| param_groups:=pg;func_lemma:= fl |} => 
            ret ((ind,(pg,fl))::lt)
        end
        )
    xs [].

End Generation.