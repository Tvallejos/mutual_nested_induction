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

Definition extendName prefix (n:name) suffix :=
    match n with 
    | nAnon => nAnon
    | nNamed id => nNamed (prefix^id^suffix)
    end.
Definition extendAname prefix n suffix:= 
    map_binder_annot (fun n => extendName prefix n suffix) n.

(*
Important things to know for de Bruijn indices:

The general shape of the induction lemma is:
∀ Params (P: ∀ Non-uni Indices (Inst: Ind params non-uni indices) -> Prop),
(H_ctor: ∀ non-uni args (possible IHs), P non-uni indice-inst (Ctor params non-uni args)) ->
∀ Non-uni Indices (Inst: Ind params non-uni indices), P non-uni indices inst :=
    λ Params P H_ctor.
    fix f non-uni indices inst : P non-uni indices inst :=
    match inst as i in (ind _ _ indices) return P non-uni _ i with
    | Ctor args => H_ctor non-uni args (proofs)
    end

A constructor of an inductive type of the form args -> conclusion (where conclusion is 'ind params non-uni indices')
is represented as:
Ind -> Params -> Non-uni -> Args -> tApp (tRel ...) ...
the inductive is virtually quantified behind the params and all params (including non-uni) are quantified before args
(and taken by lambdas in the one_inductive_body fields)

other edge cases like the lambdas in the return of a match or
the lambdas in fix point declarations are explained at the corresponding positions
*)



(* generates a list (n-1), ..., 0 *)
Fixpoint mkNums (n:nat) :=
    match n with 
    | O => []
    | S m => [m] ++ mkNums m
    end.
(* generates a list tRel (n-1), ..., tRel 0 *)
Fixpoint mkRels (n:nat) := map tRel (mkNums n).
Fixpoint mkAstRels (n:nat) := map Ast.tRel (mkNums n).

Require Import List.
Import ListNotations.
Import IfNotations.

(* can be quoted as more powerful hole (coq does not need to fill it in)
    only for testing/debugging purposes
 *)
Variable (TODO: forall {T}, T).

Inductive assumption_type {T} :=
    | Argument (asm:T) | IH (asm:T).

Variant creation_mode := IHAssumption | IHProof.

    (*
    
    output:
    fun p_pos -> lambda arg. proof
    fun f_pos -> lambda arg. proof

    call_pos - either predicate for Assumption
                or fix point function for proof

    TODO: lift contexts, ind_pos, call_pos
    *)

(* Local Instance option_moad. *)

Fixpoint create_induction_hypothesis (mode:creation_mode) (param_ctx non_uni_param_ctx indice_ctx:context) (ind_pos call_pos:nat) (t:term) : option term :=
    match t with 
    | tRel p =>
        if p =? ind_pos then
            (* skip parameters and shift call_pos accordingly to sacrificial lambdas *)
            (* holes only possible for proof *)
            if mode is IHProof then
                (* not necessary but saves from having trouble with liftings *)
                ret (it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) (tRel (#|param_ctx|+call_pos)))
            else
                ret (it_mkLambda_or_LetIn param_ctx (tRel (#|param_ctx|+call_pos)))
        else 
            None
    | tApp a b =>
        s <- create_induction_hypothesis mode param_ctx non_uni_param_ctx indice_ctx ind_pos call_pos a;;
        if mode is IHProof then
            ret (tApp s hole)
        else
            ret (tApp s b)
    | _ => None
    end.


(*
The argument is an argument list => not reversed 
    (but in correct order like you write it in the definition of the constructor)
*)
(* internal viewpoint: ∀ params P non_uni. • <- here *)
Definition augment_arguments (param_ctx non_uni_param_ctx indice_ctx:context) xs : list (@assumption_type (BasicAst.context_decl term)) := 
    let hyp arg t := IH (vass (extendAname "" arg.(decl_name) "IH_") t) in

    let dummyIH (arg:context_decl) := 
        hyp arg (TemplateToPCUIC.trans [] <% True %>) in

    (* map (Argument _) xs. (* Do nothing => case analysis *) 
        same as IHs := []
    *)
    
    fold_left_i
    (fun assumptions i arg =>
        (* behind params, P, and non-uni *)
        let ind_pos := #|param_ctx|+1+#|non_uni_param_ctx|+i in (* virtual position of the inductive type represented by tRel in the ctor arguments *) 
        let pred_pos := #|non_uni_param_ctx|+i in
        let asm := create_induction_hypothesis IHAssumption param_ctx non_uni_param_ctx indice_ctx ind_pos pred_pos arg.(decl_type) in
       
        let IHs := 
            if asm is (Some asm_body) then
                (* lift over argument *)
                [hyp arg (mkApps (lift0 1 asm_body) [tRel 0])]
                (* [dummyIH arg] *)
                (* [] *)
            else 
                []
        in
        (* let IHs := [] in *)

        assumptions++[Argument arg]++IHs
    )
    xs
    [].

(* adds quantification of context around body *)
Notation quantify:= (it_mkProd_or_LetIn)(only parsing).


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
    let AstPlaceholder := Ast.mkApp <% @TODO %> (Ast.hole) in
    let placeholder := TemplateToPCUIC.trans [] AstPlaceholder in


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


    (* compute contexts of params, params, non-uniform params, and indices *)
    let non_uniform_param_count := 1 in (* TODO: guess it correctly *)
    let ind_type := ind.(ind_type) in (* type of the inductive *)
    let (ctx,retTy) := decompose_prod_assum [] ind_type in (* get params and indices and inner retTy *)
        (* for list: ctx=[Type], retTy=Type *)
    let indice_ctx := ind.(ind_indices) in
    let all_param_ctx := skipn #|indice_ctx| ctx in (* parameters and non-uniform parameter *)
    let non_uni_param_ctx := firstn non_uniform_param_count all_param_ctx in (* non-uniform are behind => at the front *)
    let param_ctx := skipn #|non_uni_param_ctx| all_param_ctx in 


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

    (* takes argument context (that is given in constructor) in normal view => behind parameters *)
    (* the result is a list **not** a context (=> it is in the correct order as you would write it) *)
    let augmented_args arg_ctx := 
        (* internal viewpoint: ∀ params P non_uni. • <- here *)
        (*   if this viewpoint is not met, you have to lift the resulting term after using the augmented arguments *)
        (* lift over P behind non_uni parameters *)
        let arg_list := rev (lift_context 1 #|non_uni_param_ctx| arg_ctx) in (* ind is tRel (param+1) the +1 to lift over P *)
        augment_arguments param_ctx non_uni_param_ctx indice_ctx arg_list 
    in

    let case_ctx :=
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
                        (* lift over other cases for easier view *)
                        lift0 i (
                            (* viewpoint: ∀ params P. • <- here *)

                            (* lift over P *)
                            quantify (lift_context 1 0 non_uni_param_ctx)
                            (fold_right
                            (fun arg t =>
                                (* arg of type assumption_type *)
                                match arg with
                                | Argument x => mkProd_or_LetIn x t
                                | IH y => 
                                    mkProd_or_LetIn y (lift0 1 t) (* lift everything over new assumptions *)
                                end
                            )
                            (
                            (* the innerbody under ∀ non-uni args (augmented). • *)
                                let ctor_inst :=
                                    mkApps 
                                        (tConstruct inductive i uinst)
                                        (
                                            (* lift over args, non-uni, and predicate *)
                                            map (lift0 (#|arg_ctx|+#|non_uni_param_ctx|+1)) (mkRels #|param_ctx|) ++ (* params *)
                                            (* locally quantified non-uni behind args *)
                                            map (lift0 #|arg_ctx|) (mkRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                            map (lift0 0) (mkRels #|arg_ctx|) (* args *)
                                        )
                                in
                                mkApps 
                                    (* lift over args, non-uni *)
                                    (tRel (#|arg_ctx|+#|non_uni_param_ctx|)) (* predicate *)
                                    (
                                        map (lift0 #|arg_ctx|) (mkRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                        (* lift over P to reach params *)
                                        map (lift 1 (#|arg_ctx|+#|non_uni_param_ctx|) ) ind_list ++ (* index instantiation *)
                                        [ctor_inst] (* constructor instance *)
                                    )
                            )
                            (augmented_args arg_ctx)
                            (* (map Argument (rev (lift_context 1 #|non_uni_param_ctx| arg_ctx))) *)
                            )
                        )
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
    let lemma_argument_ctx := (* contexts are reversed lists *)
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
        it_mkProd_or_LetIn lemma_argument_ctx
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
        lemma_argument_ctx
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
            dtype := conclusion_type (#|case_ctx|); (* hole not possible for types without ctors *)
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
                        Ast.preturn := 
                        (* P holds with non-uni, indices, inst *)
                        (* Ast.hole not possible for types without ctors *)
                        Ast.mkApps 
                        (* local instance, indices, fix point arguments,f  *)
                        (Ast.tRel (1+#|indice_ctx|+#|predicate_ctx|+1+#|case_ctx|))
                        (
                            (* lift over instance, indices, instance (fix), indices (fix) *)
                            map (Ast.lift0 (1+#|indice_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++
                            (* lift over instance *)
                            map (Ast.lift0 1) (mkAstRels #|indice_ctx|) ++
                            (* instance *)
                            [Ast.tRel 0]
                        )

                        |}
                        (Ast.tRel 0) (* match over inductive instance in fix *)
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
                                        (*
                                        #|arg_ctx| = number of arguments of the ctor
                                        #|predicate_ctx| = inst+indices+non-uni (arguments of f)
                                        *)

                                        AstPlaceholder

                                        (* let aug_args := augmented_args arg_ctx in (* virtually behind ∀ Params P. • *)

                                        Ast.mkApps
                                        (Ast.tRel (#|arg_ctx|+#|predicate_ctx|+1+
                                                    (#|case_ctx| -i-1))) (* H_ctor *)
                                        (
                                            map (Ast.lift0 (#|arg_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++
                                            snd (
                                                fold_right
                                                (fun arg '(i,rels) =>
                                                    match arg with
                                                    | Argument _ => 
                                                        (i+1,Ast.tRel i::rels)
                                                    | IH _ => 
                                                        (i,
                                                        (
                                                            Ast.mkApps 
                                                            (Ast.tRel (#|arg_ctx| + #|predicate_ctx|)) (* f *)
                                                            (
                                                                map (fun _ => Ast.hole) (mkNums #|non_uni_param_ctx|) ++
                                                                map (fun _ => Ast.hole) (mkNums #|indice_ctx|) ++
                                                                [Ast.tRel i] (* corresponding recursive instance *)
                                                            )
                                                        ) :: rels)
                                                    end
                                                )
                                                (0,[])
                                                aug_args
                                            )
                                        ) *)

                                    )
                                ;
                                |}
                            ) ind.(ind_ctors)
                        )
                    )
                ) 
                )
            ; 
            rarg  := #|predicate_ctx| - 1 (* the last argument (the instance) is structural recursive *)
            |} ] 0
        )
        )
    )
    Cast
    (PCUICToTemplate.trans type).





Load test_types.
MetaCoq Run (
    (* t <- tmQuote (list);; *)
    (* t <- tmQuote (@Vector.t);; *)

    (* t <- tmQuote (paramTest);; *)
    (* t <- tmQuote (indexTest);; *)
    (* t <- tmQuote (depTest);; *)
    (* t <- tmQuote (implicitTest);; *)

    (* t <- tmQuote (nonUniTest);; *)
    t <- tmQuote (nonUniDepTest);;

    (fix f t := match t with
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
         tmPrint lemma;; (* this can not be read *)
         tmMkDefinition "test" lemma
    | [] => tmFail "no inductive body found"
    | _ => tmFail "too many inductive bodies (currently, mutual induction is not supported)"
    end
    | Ast.tApp t _ => f t (* resolve partial evar application *)
    | _ => tmFail "Not an inductive type, maybe try @ind for implicit arguments"
    end) t
).
Print test.