From MetaCoq.Template Require Import All.

From MetaCoq Require Import All.
Require Import String List.
Local Open Scope string.
Import ListNotations MCMonadNotation Nat.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.PCUIC Require Import PCUICToTemplate.

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

Load test_types.


MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Run (TC <- Translate nat_TC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
Inductive vec (A : Type) : nat -> Type :=
	nilVec : vec A 0
  | consVec : A -> forall n : nat, vec A n -> vec A (S n).
MetaCoq Run (TC <- Translate list_TC "vec" ;;
                tmDefinition "vec_TC" TC ).
Print vecᵗ.