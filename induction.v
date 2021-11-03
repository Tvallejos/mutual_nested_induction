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

Definition relevant_binder (n:name) :=
    {|
    binder_name := n;
    binder_relevance := Relevant
    |}.
Definition rAnon := relevant_binder nAnon.
Definition rName n := relevant_binder (nNamed n).

Definition hole := TemplateToPCUIC.trans [] hole.


(* Search Env.one_inductive_body. *)

(* Search (list term) termRR *)

(*
 arguments
 decompose_apps
 decompose_prod
    (* let '(names, types, body) := decompose_prod ind_type in *)

 mkApps

 Print it_mkProd_or_LetIn.
*)

Inductive paramTest (A:Type) (B:nat) : Type :=.
Inductive indexTest (A:Type) : nat -> bool -> Type :=.
Inductive nonUniTest (A:Type) (n:nat) : bool -> Type :=
    C: forall (H:nonUniTest A (S n) false), nonUniTest A n true.

Inductive depTest (A:Type) (HA: A -> Type) : (forall a, HA a) -> Type :=.

(*
scheme

forall 
    params 
    (P: forall 
        non-uniform
        indices,
        instance ->
        Prop
    )
    cases,
    forall 
        non-uni
        indices,
        instance ->
        P ...

*)

(* generates a list tRel (n-1), ..., tRel 0 *)
Fixpoint mkRels (n:nat) :=
    match n with 
    | O => []
    | S m => [tRel m] ++ mkRels m
    end.

Definition context_decl_map (f:term->term) (c:context_decl) :=
    {|
    decl_name := c.(decl_name);
    decl_body := option_map f c.(decl_body);
    decl_type := f c.(decl_type)
    |}.

    (* lift_context *)


Definition createInductionPrinciple (ind_term:term) (ind:one_inductive_body) :=
    (* auxiliary definitions (mostly for testing purposes) *)
    let PropQ := TemplateToPCUIC.trans [] <% Prop %> in
    let TrueQ := TemplateToPCUIC.trans [] <% True %> in
    let IQ := TemplateToPCUIC.trans [] <% I %> in

    (* remember: contexts are reversed
        decompose gives contexts
        it_mk takes contexts
     *)

     (* separate params, non-uniform params, and indices *)
    let non_uniform_param_count := 0 in
    let ind_type := ind.(ind_type) in (* type of the inductive *)
    let (ctx,retTy) := decompose_prod_assum [] ind_type in (* get params and indices and inner retTy *)
        (* for list: ctx=[Type], retTy=Type *)
    let indice_ctx := ind.(ind_indices) in
    let all_param_ctx := skipn #|indice_ctx| ctx in (* parameters and non-uniform parameter *)
    let non_uni_param_ctx := firstn non_uniform_param_count all_param_ctx in (* non-uniform are behind => at the front *)
    let param_ctx := skipn #|non_uni_param_ctx| all_param_ctx in 

    (* adds quantification of context around body *)
    let quantify ctx body := it_mkProd_or_LetIn ctx body in

    (* construct the quantifications in the predicate
       these are all non-uniform parameters, the indices, and 
       an instance of the inductive type instantiated with params and indices
       
       the context has to be liftet directly behind the parameter quantification
       using lift_context [amount] 0 predicate_ctx
       *)
    let predicate_ctx := 
        [vass (rName "ind_inst") 
            (mkApps ind_term 
            (
                map (lift0 (#|non_uni_param_ctx|+#|indice_ctx|)) (mkRels #|param_ctx|) ++ (* params *)
                map (lift0 (#|indice_ctx|)) (mkRels #|non_uni_param_ctx|) ++ (* non_uni *)
                map (lift0 0) (mkRels #|indice_ctx|) (* indices *)
            ) (* params, non-uni, and indices*)
            )] ++ 
        indice_ctx ++ (* quantify over indices *)
        non_uni_param_ctx
    in
    (* use the context to create the predicate type 
        ∀ non-uni indices, Ind params non-uni indices -> ℙ
    *)
    let predicate_type := 
        quantify predicate_ctx
        PropQ (* TODO: correct elimination *)
    in (* type of the predicate used in the induction *)

    (* the conclusion type
        ∀ non-uni indices (h:Ind params non-uni indices), P non-uni indices h
        we can see that the first part (up to and including h) is exactly the 
        predicate context (the quantifications of P)
        we, therefore, use the context as quantification 
        (alternative implementation: collect quantifications from type (possibly infered => difficult here) and repeat)
        (alternative implementation2: use holes and quantify for all arguments (holes are not possible in the type))

        lastly, compute the correct de Bruijn index of P and apply all quantifications
     *)
    let conclusion_type predicateDist :=
        (quantify
           (lift_context (S predicateDist) 0 predicate_ctx) (* [instance] ++ indice_ctx ++ non_uni_param_ctx *)
        (mkApps 
            (tRel (predicateDist + #|predicate_ctx|)) (* predicate *)
            (
                (* one lifting is for instance *)
                map (lift0 (S #|indice_ctx|)) (mkRels #|non_uni_param_ctx|) ++ (* apply locally quant. non-uniform *)
                map (lift0 1) (mkRels #|indice_ctx|) ++ (* apply locally quant. indices *)
                [tRel 0]
            )
        ))
    in

    (*
    the cases for needed for case analysis/induction
    *)
    let case_ctx :=
        (* dummy case: forall non-uni indices inst, P *)
        [
        vass (rName "H_All")
        (conclusion_type 0) (* lift over predicate *)
        ]
    in

    (*
    build the context of the type for the induction lemma
    the context contains the parameters, the predicate, and
    all cases (possibly extended with induction hypotheses)

    we do not include the conclusion quantifications here as we view them as 
    a separate section of the induction lemma 
    (this distinction becomes clear in the proof where we build a fixpoint over the
    arguments in the conclusion)
    *)
    let argument_ctx := (* contexts are reversed lists *)
        case_ctx ++
        [vass (rName "P") predicate_type] ++
        param_ctx (* quantify params *)
     in (* all arguments (params, predicate, cases) *)

     (*
     the type of the induction lemma including the conclusion
     ∀ params predicate,                                (* preamble *)
     HCase_1 -> ...                                     (* cases *)
     HCase_n ->
     ∀ non-uni indices (h:Ind params non-uni indices),  (* conclusion *)
       P non-uni indices h
     *)
    let type := 
        it_mkProd_or_LetIn argument_ctx
        (conclusion_type (#|case_ctx|) ) 
        (* (conclusion_type (1 + #|case_ctx|) )  *)
        (* lift over predicate and cases *)
    in 

    (*
    build the body (the proof)
    strictly speaking, we only need the body and need to annotate the type
    everywhere (which is possible as we have all necessary information)

    but for convenience, we cast the body to the correct type allowing for
    holes to be filled in during unquoting
    we will nevertheless annotate the types when easily possible or convenient

    take all arguments from the argument context
    (params, predicate, cases)
    and prove the induction lemma using a fixpoint over
    the conclusion with a case analysis inside

    *)
    tCast 
    (PCUICToTemplate.trans
        (it_mkLambda_or_LetIn
        argument_ctx
        (tRel 0)
        )
    )
    Cast
    (PCUICToTemplate.trans type).
    


MetaCoq Run (
    (* t <- tmQuote (@list);; *)
    (* t <- tmQuote (@Vector.t);; *)
    (* t <- tmQuote (paramTest);; *)
    (* t <- tmQuote (indexTest);; *)
    (* t <- tmQuote (depTest);; *)
    t <- tmQuote (nonUniTest);;
    match t with
    Ast.tInd {| inductive_mind := k |} _ => 
    ib <- tmQuoteInductive k;;
    match Env.ind_bodies ib with 
    | [oind] => 
        let ind_term := TemplateToPCUIC.trans [] t in
        let oindPC := TemplateToPCUIC.trans_one_ind_body [] oind in
        (* let il := getInd oindPC in *)
        t <- tmEval lazy oindPC;;
         tmPrint t;;
         tmMsg "----";;
        lemma <- tmEval lazy (createInductionPrinciple ind_term t);;
         tmPrint lemma;;
         (* tmMkDefinition "test" <% 0 %> *)
         tmMkDefinition "test" lemma
    | [] => tmMsg ""
    | _ => tmMsg ""
    end
    | _ => tmMsg ""
    (* todo: find inductive if hidden under applications (to evars) *)
    end
).
Print test.