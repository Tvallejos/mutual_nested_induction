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