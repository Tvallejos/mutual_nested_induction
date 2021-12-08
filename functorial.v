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
From MetaCoq.PCUIC Require Import PCUICToTemplate.

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

    Definition TrueQ :=
        TemplateToPCUIC.trans [] <% True %>.


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

    Variant augmentation {T:Type} := Norm (t:T) | Aug (t:T).

    Definition app_arg_list num args := map (fun x => x+num) args++mkNums num.

    (* no context *)
    Fixpoint augment (params:context) (arg1 arg2:list nat):= 
        match params with
        | x::xᵗ::xr => 
            let '((groups,arg1,arg2), aug_args) := 
                augment xr 
                    (map (fun x => x+4) arg1++[3;2])
                    (map (fun x => x+4) arg2++[3;1]) in
                ((S groups, arg1,arg2),
                    x::xᵗ::
                    (map_decl (lift0 1) xᵗ)::
                    (vass rAnon (func (tRel 1) (tRel 0) [] (lift0 2 xᵗ.(decl_type))))::
                    (mapi (fun i a => map_decl (lift 2 i) a) aug_args))
        | _ => 
        let indices := rev (indice_ctx) in
        ((0,
            app_arg_list (#|params|+#|indices|) arg1, 
            app_arg_list (#|params|+#|indices|) arg2),params++indices)
        end.

    (* Fixpoint re_lift (xs:list(@augmentation (BasicAst.context_decl term))) : list (BasicAst.context_decl term) :=
        match xs with
        | [] => []
        | Norm x::xs => x::re_lift xs
        | Aug x::xs =>
            x::mapi (fun i a =>
                map_decl (lift 1 i) a
            ) 
            (re_lift xs)
        end. *)

    Definition type_ := 
        let '((groups,arg1,arg2),aug_args) := augment (rev param_ctx) [] [] in
        let aug_args_ctx := rev (aug_args) in
        (groups,
        (* let arg1' := app_arg_list #|indice_ctx| arg1 in
        let arg2' := app_arg_list #|indice_ctx| arg2 in *)
        it_mkProd_or_LetIn 
            aug_args_ctx
        (* it_mkProd_or_LetIn 
        (
            lift_context (2*groups) 0 indice_ctx ++
            aug_param_ctx 
        )  *)
        (tProd rAnon
        (* TrueQ *)
        (* (mkApps ind_term [tRel 4;tRel 3;tRel 0]) *)
        (mkApps ind_term (map tRel arg1))
        (lift0 1 (mkApps ind_term (map tRel arg2)))
        ))
        .

    Definition functorial_type_groups :=
        on_snd PCUICToTemplate.trans type_.

    Definition type := snd type_.

    Definition functorial_type :=
    PCUICToTemplate.trans type.

    Definition functorial :=
    tCast 
    (PCUICToTemplate.trans
        placeholder
        (* (it_mkLambda_or_LetIn
        lemma_argument_ctx
        ) *)
    )
    Cast
    (PCUICToTemplate.trans type).
    
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

