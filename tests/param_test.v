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

Unset Strict Unquote Universe Mode. 
Load test_types.


MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Run (TC <- Translate nat_TC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
MetaCoq Run (TC <- Translate list_TC "vec" ;;
                tmDefinition "vec_TC" TC ).
Print vecᵗ.
MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ).
Print roseᵗ.
MetaCoq Run (TC <- Translate list_TC "rose2" ;;
                tmDefinition "rose2_TC" TC ).
Print rose2ᵗ.
MetaCoq Run (TC <- Translate list_TC "roseSA" ;;
                tmDefinition "roseSA_TC" TC ).
Print roseSAᵗ.
MetaCoq Run (TC <- Translate list_TC "roseA" ;;
                tmDefinition "roseA_TC" TC ).
Print roseAᵗ.
MetaCoq Run (TC <- Translate list_TC "bool" ;;
                tmDefinition "bool_TC" TC ).
Print boolᵗ.
MetaCoq Run (TC <- Translate bool_TC "nonUniTest" ;;
                tmDefinition "nonUniTest_TC" TC ).
Print nonUniTestᵗ.
MetaCoq Run (TC <- Translate bool_TC "nonUniDepTest" ;;
                tmDefinition "nonUniDepTest_TC" TC ).
Print nonUniDepTestᵗ.
MetaCoq Run (TC <- Translate nat_TC "guardTest" ;;
                tmDefinition "guardTest_TC" TC ).
Print guardTestᵗ.
MetaCoq Run (TC <- Translate vec_TC "list2" ;;
                tmDefinition "list2_TC" TC ).
Print list2ᵗ.
MetaCoq Run (TC <- Translate list2_TC "dNest" ;;
                tmDefinition "dNest_TC" TC ).
Print dNestᵗ.
MetaCoq Run (TC <- Translate list2_TC "dNestL" ;;
                tmDefinition "dNestL_TC" TC ).
Print dNestLᵗ.
MetaCoq Run (TC <- Translate list_TC "noRose" ;;
                tmDefinition "noRose_TC" TC ).
Print noRoseᵗ.
MetaCoq Run (TC <- Translate list_TC "con" ;;
                tmDefinition "con_TC" TC ).
Print conᵗ.
MetaCoq Run (TC <- Translate con_TC "roseCon" ;;
                tmDefinition "roseCon_TC" TC ).
Print roseConᵗ.
MetaCoq Run (TC <- Translate roseA_TC "roseRose" ;;
                tmDefinition "roseRose_TC" TC ).
Print roseRoseᵗ.

(* TODO: parametricity of typed with functions like List.app, Addition, ... *)