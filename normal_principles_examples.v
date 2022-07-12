
From MetaCoq.Induction Require Import commands.

From MetaCoq Require Import All.
Require Import String List.
Local Open Scope string.
Import ListNotations MCMonadNotation Nat.

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

Open Scope bs_scope.

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.

MetaCoq Run (createIH false nat).
Print nat_nested_ind.
Lemma addsn n : n + 0 = n.
Proof. apply nat_nested_ind.
- simpl. Abort.

MetaCoq Run (createIH false natᵗ).
Print natᵗ_nested_ind.

Lemma nat_natᵗ_tac : forall n, natᵗ n.   
Proof. fix f 1. intros n. destruct n.
    - constructor. 
    - constructor. apply f.
Qed.

Definition nat_natᵗ_fun : forall n, natᵗ n :=
    fix f n : natᵗ n :=
        match n with
        | O => Oᵗ
        | S n' => Sᵗ n' (f n')
        end.

MetaCoq Quote Recursively Definition nat_is_nat := nat_natᵗ_fun.

Lemma nat_ind_tac :
forall P : nat -> Prop,
P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.
Proof. intros P P0 PS n; apply natᵗ_nested_ind. 
    - apply P0. 
    - apply PS. 
    - apply nat_natᵗ_tac. 
Qed.

Definition nat_ind_fun :
    forall P : nat -> Prop,
        P 0 -> 
            (forall n : nat, P n -> P (S n)) ->
        forall n : nat, P n :=
    fun P H0 IH n => natᵗ_nested_ind P H0 IH n (nat_natᵗ_fun n).

(* =============== *)


MetaCoq Run (TC <- Translate nat_TC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
MetaCoq Run (createIH false listᵗ).

Print listᵗ_nested_ind.

(* you cannot derive the 'normal' induction principles for container types 
    using the parametricity translation of that type without assuming (forall a, is_A a). 
    Because you need to know the structure of the type that is parameterized (A) to get the proposition is_A
*)
(* Lemma list_ind_fun : forall (A : Type) (P : list A -> Prop),
    P nil ->
    (forall (a : A) (l : list A), P l -> P (a :: l)%list) -> 
    forall l : list A, P l :=
    fun A P P0 IH l => listᵗ_nested_ind A  *)

Lemma list_listᵗ_tac A is_A: (forall a, is_A a) -> forall x, listᵗ A is_A x.
Proof. intro HA. fix f 1. destruct x.
    - constructor.
    - constructor. apply HA. apply f.
Qed.
    
Definition list_listᵗ_fun : forall A is_A, (forall a, is_A a) -> forall x, listᵗ A is_A x:=
    fun A is_A AH =>
    fix f l : listᵗ A is_A l :=
    match l with
    | nil => nilᵗ A is_A
    | cons h t => consᵗ A is_A h (AH h) t (f t)
    end.

(* =========================== *)

Inductive rose : Prop := 
    | Leaf : rose
    | Node (xs:list rose).

MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ).
Print roseᵗ.

Definition rtree_rtreeᵗ_tac : forall t, roseᵗ t.
Proof. fix f 1. destruct t.
    - constructor.
    - constructor. apply (list_listᵗ_fun rose roseᵗ f). 
Qed.

Definition rtree_rtreeᵗ_tac2 : forall t, roseᵗ t.
Proof. fix f 1. destruct t.
    - constructor.
    - constructor. generalize xs. fix F 1. intro l. destruct l.
        + constructor.
        + constructor. apply f. apply F.
Qed.

Definition rtree_rtreeᵗ_tac3 : forall A (is_A : A -> Prop), (forall a, is_A a) -> forall t, roseᵗ t.
Proof. intros A is_A funtorial. fix f 1. destruct t.
    - constructor.
    - constructor. generalize xs. fix F 1. intro l. destruct l.
        + constructor.
        + constructor. apply f. apply F.
Qed.

Axiom todo: forall t,t.

Definition rtree_rtreeᵗ_fun : forall t, roseᵗ t:=
    fix f t : roseᵗ t := 
    match t with
    | Leaf => Leafᵗ 
    | Node xs => Nodeᵗ xs (list_listᵗ_fun rose roseᵗ f xs)
    end.

Definition rtree_rtreeᵗ_fun2 : forall t, roseᵗ t:=
    fix f t : roseᵗ t := 
    match t with
    | Leaf => Leafᵗ 
    | Node xs => Nodeᵗ xs (list_listᵗ_fun rose roseᵗ f xs)
    end.
