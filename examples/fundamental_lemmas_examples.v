From MetaCoq.Induction Require Import commands.
From MetaCoq Require Import All.
Require Import String List.
Import ListNotations MCMonadNotation Nat.

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

Open Scope bs_scope.


MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Run (create_T_is_T natᵗ nat_TC). 
Print nat_fl.

Inductive trivialterm : Type :=
| tvar 
| tapp (s t : trivialterm)
| tlam (s : trivialterm).

MetaCoq Run (TC <- Translate emptyTC "trivialterm" ;;
                tmDefinition "trivialterm_TC" TC ).
MetaCoq Run (create_T_is_T trivialtermᵗ trivialterm_TC).
Print trivialterm_fl. 

Inductive term_example : Type :=
| var (n : nat)
| app (s t : term_example)
| lam (s : term_example).

(* should the translate plugin check if the translation already exists? *)
MetaCoq Run (TC <- Translate nat_TC "term_example" ;;
                tmDefinition "term_TC" TC ).
Print term_exampleᵗ.
MetaCoq Run (create_T_is_T term_exampleᵗ term_TC).