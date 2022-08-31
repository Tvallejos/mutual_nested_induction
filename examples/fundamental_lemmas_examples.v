From MetaCoq.Induction Require Import commands.
From MetaCoq Require Import All.
Require Import String List.
Import ListNotations MCMonadNotation Nat.

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

Open Scope bs_scope.

(* === === === === === === *)
(* === CLOSED INDUCTIVES === *)
(* === === === === === === *)

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
MetaCoq Run (natfl_TC <- create_T_is_T natᵗ nat_TC;;
                tmDefinition "natfl_TC" natfl_TC ).
Check nat_fl : forall n, natᵗ n.

Inductive trivialterm : Type :=
| tvar 
| tapp (s t : trivialterm)
| tlam (l : trivialterm).

MetaCoq Run (TC <- Translate natfl_TC "trivialterm" ;;
                tmDefinition "trivialterm_TC" TC ).
MetaCoq Run (create_T_is_T trivialtermᵗ trivialterm_TC >>= tmDefinition "term_fl_TC").
Check trivialterm_fl : forall t, trivialtermᵗ t. 

(* === === === === === === *)
(* === OPEN INDUCTIVES === *)
(* === === === === === === *)

Inductive term_example : Type :=
| var (n : nat)
| app (s t : term_example) (ot : trivialterm)
| lam (l : term_example).

(* should the translate plugin check if the translation already exists? *)
MetaCoq Run (TC <- Translate term_fl_TC "term_example" ;;
                tmDefinition "term_TC" TC ).
MetaCoq Run (create_T_is_T term_exampleᵗ term_TC).
Check term_example_fl : forall t, term_exampleᵗ t. 

(* === === === === === === === === === === === *)
(* === INDUCTIVES WITH TYPE AS PARAMETERS === *)
(* === === === === === === === === === === ===*)
MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
MetaCoq Run (create_T_is_T listᵗ list_TC).
Check list_fl : forall A is_A, (forall a, is_A a) -> forall l, listᵗ A is_A l.

Inductive many_types_as_parameters (A B C D : Type) : Type :=
| MTAP (h1 : A) (h2 : B) (h3: C) (h4 : D) (t : many_types_as_parameters A B C D).

MetaCoq Run (TC <- Translate nat_TC "many_types_as_parameters" ;;
                tmDefinition "mtap_TC" TC ).
MetaCoq Run (create_T_is_T many_types_as_parametersᵗ mtap_TC).
Check many_types_as_parameters_fl : forall A is_A, (forall a, is_A a) ->
                                     forall B is_B, (forall b, is_B b) ->
                                      forall C is_C, (forall c, is_C c) ->
                                       forall D is_D, (forall d, is_D d) ->
                                        forall mtap, many_types_as_parametersᵗ A is_A B is_B C is_C D is_D mtap.

(* USING PARAMS IN ARBITRARY ORDER *)
Inductive type_and_closed_inds (A : Type) (n : nat) (B C : Type) : Type :=
| mt_taci
| some_params (c : C) (n :nat).

MetaCoq Run (TC <- Translate natfl_TC "type_and_closed_inds" ;;
                tmDefinition "taci_TC" TC ).
MetaCoq Run (create_T_is_T type_and_closed_indsᵗ taci_TC).
Check type_and_closed_inds_fl : forall A is_A, (forall a, is_A a) ->
                                 forall n is_n, True ->
                                  forall B is_B, (forall b, is_B b) ->
                                   forall C is_C, (forall c, is_C c) ->
                                    forall taci, type_and_closed_indsᵗ A is_A n is_n B is_B C is_C taci.
