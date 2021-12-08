From MetaCoq.Induction Require Import commands.

From MetaCoq Require Import All.
Require Import String List.
Local Open Scope string.
Import ListNotations MCMonadNotation Nat.

Inductive rose : Prop := Node (xs:list rose).
Inductive roseA (A:Type) : Prop := LeafA (a:A) | NodeA (xs:list (roseA A)).

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.


MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Run (TC <- Translate nat_TC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ).
Print roseᵗ.
MetaCoq Run (TC <- Translate list_TC "roseA" ;;
                tmDefinition "roseA_TC" TC ).
Print roseAᵗ.

MetaCoq Run (createIH false listᵗ).
Print listᵗ_nested_ind.
Fail MetaCoq Run (createIH false roseᵗ).
MetaCoq Run (createFunctorial false listᵗ).
MetaCoq Run (createIH false roseᵗ).
Print roseᵗ_nested_ind.
MetaCoq Run (createIH false roseAᵗ).
Print roseAᵗ_nested_ind.