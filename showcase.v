From MetaCoq.Induction Require Import commands.

From MetaCoq Require Import All.
Require Import String List.
Local Open Scope string.
Import ListNotations MCMonadNotation Nat.

Inductive rose : Prop := Node (xs:list rose).
Inductive list2 (A:Type) := nil2 | cons2 (a:A) (xs:list2 A).
Inductive roseA (A:Type) : Type := LeafA (a:A) | NodeA (xs:list2 (roseA A)).

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
    induction H using roseAᵗ_nested_ind.
    - admit.
    - admit.

Goal rose -> nat.
    intros r.
    assert (roseᵗ r).
    {
        induction r.
    }
    induction r using roseᵗ_nested_ind.