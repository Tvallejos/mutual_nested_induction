From MetaCoq.Template Require Import All.

From MetaCoq Require Import All.
Require Import String List.
(* Local Open Scope string. *)
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


(* generates a list tRel (n-1), ..., tRel 0 *)
Fixpoint mkNums (n:nat) :=
    match n with 
    | O => []
    | S m => [m] ++ mkNums m
    end.
Fixpoint mkRels (n:nat) := map tRel (mkNums n).
Fixpoint mkAstRels (n:nat) := map Ast.tRel (mkNums n).

Definition context_decl_map (f:term->term) (c:context_decl) :=
    {|
    decl_name := c.(decl_name);
    decl_body := option_map f c.(decl_body);
    decl_type := f c.(decl_type)
    |}.

    (* lift_context *)

Load test_types.



Require Import List.
Import ListNotations.


(*
general scheme

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

feel free to inspect the git history to see the different stages

*)
Definition createInductionPrinciple inductive uinst (mind:mutual_inductive_body) (ind:one_inductive_body) :=
    let ind_term := tInd inductive uinst in
    (* auxiliary definitions (mostly for testing purposes) *)
    let PropQ := TemplateToPCUIC.trans [] <% Prop %> in
    let TrueQ := TemplateToPCUIC.trans [] <% True %> in
    let IQ := TemplateToPCUIC.trans [] <% I %> in

    (* the kername of the inductive (module path and name) *)
    let kn := inductive.(inductive_mind) in
    (* environment to lookup the inductive for translation from TemplateCoq to PCUIC *)
    let lookup_env :global_env := [(
        (kn,InductiveDecl mind)
    )] in

    (* remember: contexts are reversed
        decompose gives contexts
        it_mk takes contexts
     *)

     (* separate params, non-uniform params, and indices *)
    let non_uniform_param_count := 1 in (* TODO: guess it correctly *)
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

        conclusion_type k should be equivalent to
        lift0 k (conclusion_type 0)
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

    we map with iteration count to keep track of the de Bruijn indices (distance to predicate)
    reverse is necessary as contexts are in reversed order 
    (the order of the cases does not matter 
        but it is less confusing and nicer to look at when they are in correct order)
    *)
    let case_ctx :=
        (* dummy case: forall non-uni indices inst, P *)
        [
        vass (rName "H_All")
        (conclusion_type #|ind.(ind_ctors)|) (* lift over predicate *)
        ]
        ++ 
        (rev(
            mapi (fun i ctor => 
                vass (rName ("H_"^ctor.(cstr_name))) 
                (* TODO: maybe refactor out the lifting offsets for clarity? *)
                (* TODO: a more functional way would be nested lifting *)
                ( (* type of the case assumption (in here lies (part of) the magic of induction) *)

                    (*
                        each ctor is mapped to 
                        ∀ non-uni args (possibly IH), P non-uni indices (Ctor params non-uni args)
                        the parameters are taken from the preamble of the induction lemma
                        the indice instantiation is taken from the constructor type

                        arguments are possibly augmented with additional inductive hypotheses

                        the constructor type includes quantifications to the parameters and non-uni
                        and virtually lies under a quantification of the inductive type which is 
                        represented by a tRel
                    *)

                    (* argument context for the constructor 
                        (how to obtain manually: quantifications of cstr_type without params, non-uni) 
                        the number of args is also cstr_arity *)
                    let arg_ctx := ctor.(cstr_args) in
                    (* index instantiation for the conclusion of the ctor 
                        (how to obtain manually: extract of the app from the conclusion of cstr_type) *)
                    let ind_list := ctor.(cstr_indices) in

                    (* replace floating ind reference (behind params) with inductive type (for arguments) 
                        at position prev. cases + predicate + params
                    *)
                    subst [ind_term] (i+1+#|param_ctx|)
                    (* lift non-uni params over other cases and over the predicate => directly behind params *)
                    (
                        quantify (lift_context (i+1) 0 non_uni_param_ctx) 
                        (quantify (
                                (* lift the argument parameter references (everything behind non-uni over cases and predicate) *)
                                lift_context (i+1) #|non_uni_param_ctx| arg_ctx
                            ) 
                        (
                            let ctor_inst :=
                                mkApps 
                                    (tConstruct inductive i uinst)
                                    (
                                        (* lift over args, non-uni, other cases and predicate *)
                                        map (lift0 (#|arg_ctx|+#|non_uni_param_ctx|+i+1)) (mkRels #|param_ctx|) ++ (* params *)
                                        (* locally quantified non-uni behind args *)
                                        map (lift0 #|arg_ctx|) (mkRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                        map (lift0 0) (mkRels #|arg_ctx|) (* args *)
                                    )
                            in
                            mkApps 
                                (* lift over args, non-uni, and other cases *)
                                (tRel (#|arg_ctx|+#|non_uni_param_ctx|+i)) (* predicate *)
                                (
                                    map (lift0 #|arg_ctx|) (mkRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                    ind_list ++ (* index instantiation *)
                                    [ctor_inst] (* constructor instance *)
                                )
                        ))
                    )
                )
            ) ind.(ind_ctors)
        ))
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
        (conclusion_type #|case_ctx| )  (* lift over cases to get to predicate position *)
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

    tCast only exists in TemplateCoq
    *)
    tCast 
    (PCUICToTemplate.trans
        (it_mkLambda_or_LetIn
        argument_ctx
        (
            (*
            the proof of induction is by case analysis on the inductive instance
            followed by application of the corresponding case

            we need a fixpoint for induction hypotheses which need smaller proofs
            *)

            (* take non-uni indices inst (all args for predicate => predicate context) *)
            (* TODO: common lifting offset *)
            tFix [ {|
            dname := rName "f";
            dtype := hole;
                (* predicate distance are the cases (the type does not see the fixpoint) *)
            (* conclusion_type (#|case_ctx|) *) 
                (* TODO: cases are wrong (off by one (too small)) but +1 is index out of bounds *)
            dbody := 
                it_mkLambda_or_LetIn 
                (* lift over f (recursive fixpoint function), cases, predicate *)
                (lift_context (1 + #|case_ctx| + 1) 0 predicate_ctx)

                (* match
                    TODO: write what we are doing
                    the tCase in TemplateCoq is easier than the tCase in PCUIC (too many redundant annotations)
                *)
                (
                (TemplateToPCUIC.trans lookup_env
                    (Ast.tCase
                        {|
                        ci_ind := inductive;
                        ci_npar := #|all_param_ctx|;
                        ci_relevance := Relevant
                        |}
                        {|
                        Ast.puinst := uinst;
                        Ast.pparams := 
                            map (Ast.lift0 
                                (* instance, indices, non-uni, f,
                                   cases, predicate
                                 *)
                                (1+#|indice_ctx|+#|non_uni_param_ctx|+1+#|case_ctx|+1)) 
                                (mkAstRels #|param_ctx|) ++
                            (* instance and indices to reach non-uni in fix point definition *)
                            map (Ast.lift0 (1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|)
                        ;
                        Ast.pcontext := 
                            map (fun _ => rAnon) indice_ctx ++
                            [rName "inst"];
                            (* there are new binders for the indices and instance in the return type *)
                        Ast.preturn := Ast.hole (* P holds with non-uni, indices, inst *)
                        |}
                        (Ast.tRel 0)
                        (
                            (* iteration count for managing which case assumption to call *)
                            mapi (fun i ctor =>
                                let arg_ctx := ctor.(cstr_args) in
                                {|
                                Ast.bcontext := 
                                    (* args is a context (reversed) but we want names in order *)
                                    map decl_name (rev arg_ctx) ;
                                Ast.bbody := 
                (
                    Ast.mkApps 
                    (Ast.tRel ( #|arg_ctx| + #|predicate_ctx|+1)) (* H_All = args+f *)
                    (map (Ast.lift0 #|arg_ctx|) (mkAstRels #|predicate_ctx|)) 
                        (* non-uni *) (* indices *) (* inst *)
                )
                                ;
                                |}
                            ) ind.(ind_ctors)
                        )
                    )
                ) 

                (* (mkApps 
                    (tRel ( #|predicate_ctx|+1)) (* H_All = args+f *)
                    (mkRels #|predicate_ctx| (* non-uni *) (* indices *) (* inst *)
                    )
                ) *)
                (* IQ *)
                )
            ; 
            rarg  := #|predicate_ctx| - 1 (* the last argument (instance) is structural recursive *)
            |} ] 0
        )
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
    (* t <- tmQuote (nonUniTest);; *)
    t <- tmQuote (nonUniDepTest);;
    match t with
    Ast.tInd ({| inductive_mind := k |} as inductive) uinst => 
    ib <- tmQuoteInductive k;;
    match Env.ind_bodies ib with 
    | [oind] => 
        let mindPC := TemplateToPCUIC.trans_minductive_body [] ib in
        let oindPC := TemplateToPCUIC.trans_one_ind_body [] oind in
        (* let il := getInd oindPC in *)
         tmMsg "==============";;
         tmMsg "===Ind term===";;
         tmMsg "==============";;
         tmPrint (tInd inductive uinst);;
         tmMsg "==============";;
         tmMsg "===Ind type===";;
         tmMsg "==============";;
        mind <- tmEval lazy mindPC;;
        t <- tmEval lazy oindPC;;
         tmPrint t;;
         tmMsg "===============";;
         tmMsg "===Ind lemma===";;
         tmMsg "===============";;
        lemma <- tmEval lazy (createInductionPrinciple inductive uinst mind t);;
         (* tmPrint lemma;; *) (* this can not be read *)
         tmMkDefinition "test" lemma
    | [] => tmFail "no inductive body found"
    | _ => tmFail "too many inductive bodies (currently, mutual induction is not supported)"
    end
    | _ => tmFail "Not an inductive type, maybe try @ind for implicit arguments"
    (* Todo: find inductive if hidden under applications (to evars) *)
    end
).
Print test.