Require Import String List.
Local Open Scope string.
Import ListNotations Nat.

Inductive paramTest (A:Type) (B:nat) : Type :=.
Inductive indexTest (A:Type) : nat -> bool -> Type :=.
Inductive nonUniTest (A:Type) (n:nat) : bool -> Type :=
    | C1: forall (H:nonUniTest A (S n) false), nonUniTest A n true
    | C2: forall (H:nonUniTest A n true), nonUniTest A n false.

Inductive nonUniDepTest (A:Type) (N:nat) (*non-uni:*) (xs:list A) : bool -> nat -> Type :=
    | CD1: forall (H1:nonUniDepTest A N [] false 1) (a:A) (M:nat) (H2:nonUniDepTest A N [] false 0), nonUniDepTest A N xs true N
    | CD2: forall (k:nat) 
    (f:forall (a:A), nonUniDepTest A N [] true 0) 
    (g:forall b, nonUniDepTest A N [] b 0)
    (h:forall n b, nonUniDepTest A N [] b n)
    (a:A)
    (HA:nonUniDepTest A N (a::xs) true 0), nonUniDepTest A N xs false 1.
    (* (HA:nonUniDepTest A N (xs ++ xs) true 0), nonUniDepTest A N xs false 1. *)

Inductive depTest (A:Type) (HA: A -> Type) : (forall a, HA a) -> Type :=.
Inductive implicitTest {n:nat} (A:Type) : Type := Impl.
Inductive guardTest := 
  G (g:nat -> guardTest).

Inductive vec (A : Type) : nat -> Type :=
	nilVec : vec A 0
  | consVec : A -> forall n : nat, vec A n -> vec A (S n).
Inductive list2 (A : Type) : Type :=
	nil2
  | cons2 (a:A) (xs:list2 A).
  (* universe constraints in parametricity (original) *)
Inductive noRose : Prop := NoNode (xs:list nat).
Inductive rose : Prop := Node (xs:list rose).
Inductive rose2 : Prop := Node2 (xs:list rose2) | Leaf2.
Inductive roseSA (A:Type) : Prop := LeafSA (a:A).
Inductive roseA (A:Type) : Prop := LeafA (a:A) | NodeA (xs:list (roseA A)).
Inductive dNest (A:Type) : Prop := DN (n:nat) (H:vec (list2 (dNest A)) n).
Inductive dNestL (A:Type) : Prop := DNL (H:list (list (dNestL A))).