From MetaCoq.Induction Require Import commands.

From MetaCoq Require Import All.
Require Import String List.
Local Open Scope string.
Import ListNotations MCMonadNotation Nat.

Inductive rose : Prop := 
    | Leaf : rose
    | Node (xs:list rose).
Inductive list2 (A:Type) := nil2 | cons2 (a:A) (xs:list2 A).
Inductive roseA (A:Type) : Type := LeafA (a:A) | NodeA (xs:list2 (roseA A)).

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

Open Scope bs_scope.

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Quote Recursively Definition nat_translation := natᵗ.
MetaCoq Run (createIH false nat).
Print nat_nested_ind.
Lemma addsn n : n + 0 = n.
Proof. apply nat_nested_ind.
- simpl. Abort.

MetaCoq Run (createIH false natᵗ).
Print natᵗ_nested_ind.

(* fun (P : nat -> Prop) (H_Oᵗ : P 0) (H_Sᵗ : forall H : nat, P H -> P (S H)) =>
fix f (H : nat) (instᵗ : natᵗ H) {struct instᵗ} : P H :=
  match instᵗ in (natᵗ inst) return (P inst) with
  | Oᵗ => H_Oᵗ
  | Sᵗ x x0 => H_Sᵗ x (f x x0)
  end
	 : forall P : nat -> Prop,
       P 0 ->
       (forall H : nat, P H -> P (S H)) -> forall H : nat, natᵗ H -> P H

fun (P : nat -> Prop) (H0 : P 0(IH : forall n : nat, P n -> P (S n))
  (n : nat) => natᵗ_nested_ind P H0 IH n (nat_natᵗ_fun n)
	 : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
 *)

MetaCoq Quote Recursively Definition natind := natᵗ_nested_ind.

MetaCoq Run (TC <- Translate nat_TC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ).
Print roseᵗ.
MetaCoq Run (TC <- Translate list_TC "list2" ;;
                tmDefinition "list2_TC" TC ).
MetaCoq Run (TC <- Translate list2_TC "roseA" ;;
                tmDefinition "roseA_TC" TC ).
Print roseAᵗ.
MetaCoq Run (createIH false listᵗ).
MetaCoq Run (createIH false list2ᵗ).
Print listᵗ_nested_ind.
Fail MetaCoq Run (createIH false roseᵗ).
MetaCoq Run (createFunctorial false listᵗ).
MetaCoq Run (createIH false roseᵗ).
Print roseᵗ_nested_ind.
MetaCoq Run (createFunctorial false list2ᵗ).
MetaCoq Run (createIH false roseAᵗ).
Print roseAᵗ_nested_ind.


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

MetaCoq Quote Recursively Definition nat_ind_tc := nat_natᵗ_fun.

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

MetaCoq Quote Recursively Definition nat_normal_ind := nat_ind_fun.

Lemma list_listᵗ_tac A is_A: (forall a, is_A a) -> forall x, listᵗ A is_A x.
Proof. intro HA. fix f 1. destruct x.
    - constructor.
    - constructor. apply HA. apply f.
Qed.
    
Definition list_listᵗ_fun : forall A is_A, (forall a, is_A a) -> forall x, listᵗ A is_A x:=
    fix f A is_A AH l : listᵗ A is_A l :=
    match l with
    | nil => nilᵗ A is_A
    | cons h t => consᵗ A is_A h (AH h) t (f A is_A AH t)
    end.

Definition rtree_rtreeᵗ_tac : forall A (is_A : A -> Prop), (forall a, is_A a) -> forall t, roseᵗ t.
Proof. intros A is_A funtorial. fix f 1. destruct t.
    - constructor.
    - constructor. apply (list_listᵗ_fun rose roseᵗ f). 
    Abort.


Definition rtree_rtreeᵗ_tac2 : forall A (is_A : A -> Prop), (forall a, is_A a) -> forall t, roseᵗ t.
Proof. intros A is_A funtorial. fix f 1. destruct t.
    - constructor.
    - constructor. generalize xs. fix F 1. intro l. destruct l.
        + constructor.
        + constructor. apply f. apply F.
Qed.
(* you cannot derive the 'normal'
 induction principles for container types 
    using the parametricity translation of that type. Because you need to know the
    structure of the type that is parameterized (A) to get the proposition is_A
*)
(* Lemma list_ind_fun : forall (A : Type) (P : list A -> Prop),
    P nil ->
    (forall (a : A) (l : list A), P l -> P (a :: l)%list) -> 
    forall l : list A, P l :=
    fun A P P0 IH l => listᵗ_nested_ind A  *)

Lemma list2_list2ᵗ A P: (forall a, P a) -> forall x, list2ᵗ A P x.
    induction x;constructor;auto.
Defined.

Lemma app_list (A : Type) (l1 l2 : list A) : map id (l1 ++ l2) = app l1 l2.
Proof. induction l1 using listᵗ_nested_ind.

listᵗ_nested_ind
Lemma roseA_roseAᵗ A P: (forall a, P a) -> forall x, roseAᵗ A P x.
Admitted.

Goal roseA nat -> True.
    intros r.
    assert(roseAᵗ nat natᵗ r).
    {
        assert(forall n, natᵗ n).
        {
            induction n;constructor;auto.
        }

    }
    Admitted.


Goal roseA nat -> True.
    intros r.
    assert(roseAᵗ nat natᵗ r).
    {
        induction r.
        - constructor. induction a;constructor;auto.
        - constructor.
          induction xs.
          + constructor.
          + constructor.
    admit.
    }
    Admitted.
(*     induction H using roseAᵗ_nested_ind.
    - admit.
    - admit. *)

Goal rose -> nat.
    intros r.
    assert (roseᵗ r).
    {
        induction r.
    }
    Admitted. 
(*     induction r using roseᵗ_nested_ind. *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenSn : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| oddSn : forall n, even n -> odd (S n).

Scheme even_ind' := Induction for even Sort Prop
  with odd_ind' := Induction for odd Sort Prop.

Fail MetaCoq Run (createIH true even).

Inductive nz (n : nat) :=
  | C : forall m, n = (S m) -> nz n.

MetaCoq Run (TC <- Translate nat_TC "Coq.Init.Logic.eq" ;;
                tmDefinition "eq_TC" TC ).

MetaCoq Run (TC <- Translate eq_TC "nz" ;;
                tmDefinition "nz_TC" TC ).
MetaCoq Run (createIH true nzᵗ).
Print nz_ind.
Print nzᵗ_nested_ind.

(* Metacoq Run Scheme nz_ind' := Induction for nz. *)
(* forall (n : nat) (P : nz n -> Prop),
       (forall (m : nat) (e : n = S m), P (C n m e)) ->
       forall n0 : nz n, P n0

forall (n : nat) (nᵗ : natᵗ n) (P : nz n -> Prop),
       (forall (m : nat) (mᵗ : natᵗ m) (H : n = S m),
        eqᵗ nat natᵗ n nᵗ (S m) (Sᵗ m mᵗ) H -> P (C n m H)) ->
       forall H : nz n, nzᵗ n nᵗ H -> P H *)
    
Lemma nznonzero : forall n , nz n -> n <> 0.
       unfold not; intros n nz nis0. induction nz. rewrite e in nis0; discriminate.
Qed.

Lemma nznonzero' : forall n , nz n -> n <> 0.

       intros n nz. induction nz using nzᵗ_nested_ind.
        - rewrite e in nis0; discriminate.
Qed.
