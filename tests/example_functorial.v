Load param_test.

Definition listᵗ_func_
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a)  :=
    fix f (x :list A) (xᵗ:listᵗ A Aᵗ x) : listᵗ A Aᵗ' x :=
    match xᵗ with
    | nilᵗ => nilᵗ A Aᵗ'
    | consᵗ y yᵗ yr yrᵗ => consᵗ A Aᵗ' y (F_A y yᵗ) yr (f yr yrᵗ)
    end
    .

Definition listᵗ_func 
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a) 
    (x:list A) 
    (xᵗ:listᵗ A Aᵗ x) : listᵗ A Aᵗ' x.
    induction xᵗ;constructor;auto.
    Defined.

Definition list2ᵗ_func 
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a) 
    (x:list2 A) 
    (xᵗ:list2ᵗ A Aᵗ x) : list2ᵗ A Aᵗ' x.
    induction xᵗ;constructor;auto.
    Defined.

(* Goal forall n (H:natᵗ n) (H2:natᵗ n), H -> H2. *)
    (* (nᵗ':natᵗ n) (F_n: True -> True -> True)  (* F_n: nᵗ -> nᵗ' *)
    *)
Definition conᵗ_func 
    (* params *)
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a) 
    (* (n:nat) (nᵗ:natᵗ n) (nᵗ':natᵗ n) (F_n: True -> True -> True) *)
    (n:nat) (nᵗ:natᵗ n) (nᵗ':natᵗ n) (F_n: True)
    (* indices *)
        (x:con A n) 
    (xᵗ:conᵗ A Aᵗ n nᵗ x) : conᵗ A Aᵗ' n nᵗ' x.
induction xᵗ.
- constructor.
- constructor; auto.
Defined.

Definition vecᵗ_func 
    (* params *)
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a) 
    (* indices *)
    (n:nat) (nᵗ:natᵗ n) 
        (x:vec A n) 
    (xᵗ:vecᵗ A Aᵗ n nᵗ x) : vecᵗ A Aᵗ' n nᵗ x.
induction xᵗ.
(* From Equations Require Import Equations. *)
- constructor.
- constructor;auto.
Defined.

Definition roseA_nest_ind :=
  fun (A : Type) (Aᵗ : A -> Type) (P : roseA A -> Prop)
  (H_LeafAᵗ : forall a : A, Aᵗ a -> P (LeafA A a))
  (H_NodeAᵗ : forall xs : list (roseA A),
	          listᵗ (roseA A) P xs -> P (NodeA A xs)) =>
fix f (H : roseA A) (instᵗ : roseAᵗ A Aᵗ H) {struct instᵗ} : P H :=
  match instᵗ in (roseAᵗ _ _ H0) return (P H0) with
  | @LeafAᵗ _ _ a aᵗ => H_LeafAᵗ a aᵗ
  | @NodeAᵗ _ _ xs xsᵗ =>
      H_NodeAᵗ xs (listᵗ_func (roseA A) (roseAᵗ A Aᵗ) P f xs xsᵗ)
  end.

Definition roseAᵗ_func 
    (A:Type) (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A:forall a, Aᵗ a -> Aᵗ' a) 
    (x:roseA A) 
    (xᵗ:roseAᵗ A Aᵗ x) : roseAᵗ A Aᵗ' x.
    induction xᵗ using roseA_nest_ind;constructor;auto.
Defined.

Definition listᵗ_inductive := 
    {| inductive_mind := (MPfile ["induction"], "listᵗ"); inductive_ind := 0 |}.
Definition list2ᵗ_inductive := 
    {| inductive_mind := (MPfile ["induction"], "list2ᵗ"); inductive_ind := 0 |}.
Definition vecᵗ_inductive := 
    {| inductive_mind := (MPfile ["induction"], "vecᵗ"); inductive_ind := 0 |}.
Definition conᵗ_inductive := 
    {| inductive_mind := (MPfile ["induction"], "conᵗ"); inductive_ind := 0 |}.
Definition roseAᵗ_inductive := 
    {| inductive_mind := (MPfile ["induction"], "roseAᵗ"); inductive_ind := 0 |}.

Load functorial_lookup.

Instance listᵗ_func_inst : functorial_instance (listᵗ_inductive) :=
    {|
        param_groups := 1;
        func_lemma := TemplateToPCUIC.trans [] <% listᵗ_func %>
    |}.
Instance list2ᵗ_func_inst : functorial_instance (list2ᵗ_inductive) :=
    {|
        param_groups := 1;
        func_lemma := TemplateToPCUIC.trans [] <% list2ᵗ_func %>
    |}.
Instance vecᵗ_func_inst : functorial_instance (vecᵗ_inductive) :=
    {|
        param_groups := 1;
        func_lemma := TemplateToPCUIC.trans [] <% vecᵗ_func %>
    |}.
Instance conᵗ_func_inst : functorial_instance (conᵗ_inductive) :=
    {|
        param_groups := 2;
        func_lemma := TemplateToPCUIC.trans [] <% conᵗ_func %>
    |}.
Instance roseAᵗ_func_inst : functorial_instance (roseAᵗ_inductive) :=
    {|
        param_groups := 2;
        func_lemma := TemplateToPCUIC.trans [] <% roseAᵗ_func %>
    |}.

(* Definition lookup_table : list (inductive * (nat * term)) := 
    [
            (* 1 group of params *)
        (listᵗ_inductive,(1,TemplateToPCUIC.trans [] <% listᵗ_func %>));
        (list2ᵗ_inductive,(1,TemplateToPCUIC.trans [] <% list2ᵗ_func %>));
            (* 1 group of params *)
        (vecᵗ_inductive,(1,TemplateToPCUIC.trans [] <% vecᵗ_func %>));
            (* 2 group of params *)
        (conᵗ_inductive,(2,TemplateToPCUIC.trans [] <% conᵗ_func %>));
        (roseAᵗ_inductive,(1,TemplateToPCUIC.trans [] <% roseAᵗ_func %>))
    ]. *)

Import Nat.
Local Open Scope nat.
From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

Definition hole := tEvar fresh_evar_id [].