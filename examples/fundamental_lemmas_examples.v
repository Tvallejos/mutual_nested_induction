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
MetaCoq Run (create_T_is_T natᵗ). 
Print nat_fl.

Inductive trivialterm : Type :=
| tvar 
| tapp (s t : trivialterm)
| tlam (s : trivialterm).

MetaCoq Run (TC <- Translate emptyTC "trivialterm" ;;
                tmDefinition "trivialterm_TC" TC ).
MetaCoq Run (create_T_is_T trivialtermᵗ).
Print trivialterm_fl. 