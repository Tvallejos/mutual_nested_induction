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


Load Test_Types.


MetaCoq Quote Definition f1 :=
    (fun (n:nat) =>
    fix f (m:nat) (k:nat) := 
    match k with 
    O => true
    | S l => true && f m l
    end).

MetaCoq Quote Definition f2 :=
    (fun A (xs:list A) =>
    match xs with
    | [] => true
    | _ => false 
    end).

MetaCoq Quote Definition f3 :=
    (fun A N (xs:list A) (h:nonUniDepTest A N xs true 0) =>
    match h return bool with (* without return bool, the MC term gets large *)
    | CD1 H1 H2 => true
    | CD2 H1 => false 
    end).

MetaCoq Quote Definition f4 :=
    (fun A (h:indexTest A 0 true) =>
    match h return bool with (* without return bool, the MC term gets large *)
    end).

MetaCoq Quote Definition f5 :=
    (fun 
    A N (P:forall xs b n, nonUniDepTest A N xs b n -> Prop)
    (HCD1: forall xs H1 H2, P xs true 0 (CD1 A N xs H1 H2))
    (HCD2: forall xs H1, P xs false 1 (CD2 A N xs H1)) =>
    fix f xs b n i : P xs b n i := 
    match i as j in nonUniDepTest _ _ _ c m return P xs _ _ j with
    | CD1 H1 H2 => HCD1 xs H1 H2
    | CD2 H1 => HCD2 xs H1
    end
    ).

MetaCoq Quote Definition f6 :=
    (fun 
    A N (P:forall xs b n, nonUniDepTest A N xs b n -> Prop)
    (HCD1: forall xs H1 (IH_H1: P [] false 1 H1) H2 (IH_H2: P [] false 0 H2), P xs true 0 (CD1 A N xs H1 H2))
    (HCD2: forall xs H1 (IH_H1: P (xs ++ xs)%list true 0 H1), P xs false 1 (CD2 A N xs H1)) =>
    fix f xs b n i : P xs b n i := 
    match i as j in nonUniDepTest _ _ _ c m return P xs _ _ j with
    | CD1 H1 H2 => HCD1 xs H1 (f _ _ _ H1) H2 (f _ _ _ H2)
    | CD2 H1 => HCD2 xs H1 (f _ _ _ H1)
    end
    ).

Print f6.