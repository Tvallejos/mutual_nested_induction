(**
Creates functorial lemmas that the parametricity translation
behaves like a functor in respect to its parameters

Application: When proving the induction lemma, 
one encounters the problem that the parametricity translation argument
listᵗ rose roseᵗ H is given stating that the property roseᵗ holds for all rose
trees in the list. But we want the nested inductive hypothesis
listᵗ rose P H that the property P under consideration in the induction
holds for all trees in the list.
Therefore, we need to translate the proofs of roseᵗ to P.
This is possible for two reasons:
* The inductive proof transforms roseᵗ instances into proofs of P
    (we state that P holds for all roseᵗ)
* Secondly, the parametricity translation of a container simply boundles
    all proofs for the elements in it.
  Therefore, all proofs can be replaced for another property, and thus,
  the parametricity translation of a container behaves like a functor.

Note: The substitution of P for roseᵗ makes it clear why
    the induction does not carry the roseᵗ instances in the predicate
    as such handling for nested types would no longer be possible.
    Additionally, the generates lemma is less cluttered as it is ultimately
    a lemma for rose not roseᵗ.

example:
listᵗ A Aᵗ x
with A:Type, Aᵗ:A->Type, x:list A

the functorial lemma has type:
∀ A (Aᵗ:A->Type) (Aᵗ':A->Type) (F_A: ∀ (a:A), Aᵗ a -> Aᵗ' a)
(x:list A),
listᵗ A Aᵗ x -> listᵗ A Aᵗ' x

Note:
A->Type can be viewed as (Typeᵗ A)

For each pair of parameter and translation another translation as destination
is introduced together with a function stating the translation property for this paramter.
This property will be recursively instantiated in the proofs.
If the parameter has no arguments or does not result in a sort, a dummy value like True
is introduced as each parametricity translated argument contains the same information.

The indices contain no further information needed to be transferred between instances.
They do not possess a functorial nature as they are dictated by inversion.
Therefore, they are carried over.
A special indice is the instance of the original type (list in the example above).
But this instance does not need any special care.

*)
Require Import util.

From MetaCoq.Template Require Import All.

From MetaCoq Require Import All.
Require Import String List.
(* Local Open Scope string. *)
Import ListNotations Nat.
Import MCMonadNotation.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.PCUIC Require Import PCUICToTemplate PCUICAst.

From MetaCoq.Induction Require Import util.
Section Functorial.

    Variable 
        (inductive:inductive)
        (uinst:Instance.t)
        (mind:mutual_inductive_body)
        (ind:one_inductive_body).

    Definition ind_term := tInd inductive uinst.

    Definition non_uniform_param_count := 0. (* should not matter here *)
    Definition ind_type := ind.(ind_type). (* type of the inductive *)
    Definition ctx_retTy := decompose_prod_assum [] ind_type. (* get params and indices and inner retTy *)
    Definition ctx := ctx_retTy.1.
    Definition retTy := ctx_retTy.2.
        (* for list: ctx=[Type], retTy=Type *)
    Definition indice_ctx := ind_indices ind.
    Definition all_param_ctx := skipn #|indice_ctx| ctx. (* parameters and non-uniform parameter *)
    Definition non_uni_param_ctx := firstn non_uniform_param_count all_param_ctx. (* non-uniform are behind => at the front *)
    Definition param_ctx := skipn #|non_uni_param_ctx| all_param_ctx. 
    


    (*
    given an argument Aᵗ generates the functorial property term
    for ∀, copy the binder and remember to apply the arguments
    for Sort, generate Aᵗ args -> Aᵗ' args 
    Otherwise generate True
     *)
        (* this is something like parametricity itself *)
    Fixpoint func x y args t :=
        match t with
        | tSort univ => 
            tProd rAnon (mkApps x args) (mkApps (lift0 1 y) (map (lift0 1) args))
        | tProd na a b =>
            tProd na a (
                func (lift0 1 x) (lift0 1 y) (map (lift0 1) args ++ [tRel 0]) b
            )
        | _ => TrueQ
        end.



    (* no context but list of params *)
    (* 
    for params A, Aᵗ add Aᵗ' and F_A
    takes list of param applications for the original and transformed term
    returns the number of parameter groups, the list of argument applications
    as number for the binder and lastly the list of new arguments (params & indices)
     *)
    Fixpoint augment (params:context) (arg1 arg2:list nat):= 
        match params with
        | x::xᵗ::xr => 
            let '((groups,arg1,arg2), aug_args) := 
                augment xr 
                    (map (fun x => x+4) arg1++[3;2])
                    (map (fun x => x+4) arg2++[3;1]) in
                ((S groups, arg1,arg2),
                    x::xᵗ::
                    (map_decl (lift0 1) xᵗ):: (* Aᵗ' *) 
                    (vass rAnon (func (tRel 1) (tRel 0) [] (lift0 2 xᵗ.(decl_type)))):: (* F_A *)
                    (mapi (fun i a => map_decl (lift 2 i) a) aug_args))
        | _ => 
        let indices := rev (indice_ctx) in
        ((0,
            app_arg_list (#|params|+#|indices|) arg1, 
            app_arg_list (#|params|+#|indices|) arg2),params++indices)
        end.

        (* computes number of param groups and type of the functorial property *)
    Definition type_ := 
        let '((groups,arg1,arg2),aug_args) := augment (rev param_ctx) [] [] in
        let aug_args_ctx := rev (aug_args) in
        (groups,
        it_mkProd_or_LetIn 
            aug_args_ctx
        (tProd rAnon
        (mkApps ind_term (map tRel arg1))
        (lift0 1 (mkApps ind_term (map tRel arg2)))
        ))
        .

    Definition functorial_type_groups :=
        on_snd PCUICToTemplate.trans type_.

    Definition type := snd type_.

    Definition functorial_type :=
    PCUICToTemplate.trans type.

    (*
    Generation of the functorial property 
    currently, the properties are only realized 
    using obligations
     *)
    (* Definition functorial :=
    tCast 
    (PCUICToTemplate.trans
        placeholder
        (* (it_mkLambda_or_LetIn
        lemma_argument_ctx
        ) *)
    )
    Cast
    (PCUICToTemplate.trans type). *)
    
End Functorial.


Ltac ind_on_last :=
  lazymatch goal with
  | |- forall x y, ?H => intros ?;ind_on_last
  | |- forall y, ?H => 
      let inst := fresh "x" in
      intros inst;induction inst (* using database *)
  | _ => fail "not applicable"
  end.
Global Obligation Tactic := cbn;ind_on_last;econstructor;auto.

