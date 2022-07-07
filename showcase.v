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


Lemma nz : forall n ,nonzero n -> n <> 0.
    unfold not; intros n nz nis0; inversion nz; rewrite nis0 in H; discriminate H. 
Qed.

Print list.
Inductive roses : nat -> Prop :=
| Noder : forall n (xs : list (even' n)), roses n
with even' : nat -> Prop :=
| even0' : forall n (r: roses n), even' 0
| evenSn' : forall n (xs : list (roses n)), odd' n -> even' (S n)
with odd' : nat -> Prop :=
| oddSn' : forall n (xs : list (roses n)), even' n -> odd' (S n).

MetaCoq Run (TC <- Translate list_TC "roses" ;;
                tmDefinition "roses_TC" TC ).

MetaCoq Run (TC <- Translate nat_TC "even" ;;
                tmDefinition "even_TC" TC ).
MetaCoq Run (createIH true evenᵗ).

Print rosesᵗ.
Print even'ᵗ.
Print natᵗ.
Check (odd'ᵗ 1 (Sᵗ 0 Oᵗ) (oddSn' 0 _ (even0' 0 _))) : Prop.