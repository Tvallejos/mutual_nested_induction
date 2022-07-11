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


Lemma nat_natᵗ n: natᵗ n.
    induction n;constructor;auto.
Defined.

Lemma list_listᵗ A P: (forall a, P a) -> forall x, listᵗ A P x.
    induction x;constructor;auto.
Defined.

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
