(*
created using github coq-8.13 branch (f000a1d66428370ac98685fb8aaca79c225a91c0)
not opam coq-metacoq 1.0~beta2+8.13
    as the opam version has less useful definitions for inductive types, cases, ...

For a more intuive (but in parts slightly longer) implementation of induction
with many explanations see
https://github.com/NeuralCoder3/nested_induction_v2/blob/main/induction.v
*)

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

Require Import util.

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


We create a special kind of induction lemma as we transform an induction lemma for the parametricity translation
Therefore, some additional assumptions are introduced and all inductive hypotheses result from replacing the 
parametricity translation of the type with the predicate in a translated argument
*)



Require Import List.
Import ListNotations.
Import IfNotations.



Section IH.

(*
Table to look up functorial instances for an inductive
the entry contains the number of parameter groups a well as 
the term of the lemma
*)
Variable (lookup_table : list (inductive * (nat * term))).
Variable verbose : bool.


Definition sacrificial_lambda (n k j : nat) (Γ : context) : term :=
    let lifted_ctx := (lift_context n k Γ) in
    it_mkLambda_or_LetIn lifted_ctx (tRel j).


(* 
get an inductive hypothesis by replacing the occurence of the parametricity translation
with the predicate
*)
(* 3.1 E.Tassi *)
Definition get_hypothesis param_ctx (ind_pos:nat) (pred_pos:nat) (t:term) :=
    let param_pos := pred_pos + 1 in
        (* sacrificial lambda to remove param application for the predicate *)
        (* holes are not allowed here but we could eagerly perform beta reduction *)
        (* predicate behind other cases and sacrificial lambdas *)
    let sacr_lam := sacrificial_lambda param_pos 0 pred_pos param_ctx in
    local_subst [sacr_lam] ind_pos t.

Definition empty_env := PCUICProgram.build_global_env_map {| universes := ContextSet.empty ; declarations := [] |}.
(*
generates the proofs
for an inductive hypothesis, the fixpoint is used to translate the 
parametricity translation instance into a proof of P
for nested occurences the functorial lemma is used to lift this transformation
*)
(* E.Tassi 5.4 *)
Fixpoint create_proof_term_ (fuel:nat) (param_ctx non_uni_param_ctx indice_ctx:context) (ind_pos pred_pos call_pos:nat) (t:term) : option term :=
    match fuel with
    | 0 => None
    | S m =>
    let create_proof_term := create_proof_term_ m in
    match t with 
    | tRel p =>
        (*
        a tRel is a reference to some argument/parameter/... in the inductive type
        *)
        if p =? ind_pos then
            (*
            if the tRel points to ind_pos, 
            this term is a self reference => induction is possible

            we want to replace it with an application to P/f (the fixpoint) which is tRel call_pos
            but these functions only expect the non_uni params, indices and the instance not the parameters
            but the inductive type is fully instantiated with the params, the non_uni (or instantiations thereof),
                and the indices
            
            therefore, we consume all parameters using lambdas without usage of there argument
            the resulting term takes all params and leaves and (eta-reduces) term of type 
                P: ∀ non_uni indices inst, Type (for assumptions)
                f: ∀ non_uni indices inst, P non_uni indices inst (for proofs)
            
            due to the new lambdas, #|param_ctx| has to be added to the call_pos because the call lies under the new lambdas

            strictly speaking, we have to give correct types to the lambdas that take the parameters although their instantiation is clear
                with correct lifting (only easy for assumptions), this is param_ctx
                alternatively, we could place dummy values in the lambdas and using eager
                    application with lambda instantiation (mkEagerApp), we could fill them in during construction
                    resulting in a lambda free resulting term
                for proofs we are free to use holes (even without mkEagerApp) as the cast in the later usage 
                    guarantees an instantiation of the evars

            read on in the tApp case to see how the instantiation of non_uni and indices is correctly computed
            (reminder: the instantiation of the instance is outside the lemma and is the task of the caller)
            *)

            (* skip parameters and shift call_pos accordingly to sacrificial lambdas *)
            (* holes only possible for proof *)
            (* TODO: move sacrificial lambda outside (see local stashed commit) *)
            (* not necessary to have holes but saves us from having trouble with liftings *)
            ret (it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) (tRel (#|param_ctx|+call_pos)))
        else 
            (* anything else like params, references arguments, ... do not allow for induction *)
            (* ret (it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) (tRel (#|param_ctx|+call_pos))) *)
            None


    | tApp a b =>
        (*
        when computing the induction hypothesis for an argument
        we encounter 'ind (as tRel) params non_uni indices' => many applications around the main center of the inductive
        one possibility is to decompose the application, skip the params, subst the core, and recompose it
        but this is not generalizable to guarded induction and nested induction

        therefore, we write a more general and local mapping by traversal

        if we encounter an application (with the params, non_uni, or indices) we recurse in the
            core of the application to compute the induction hypothesis and reapply the application argument
        this guarantees that we reapply all non_uni and indices (necessary) but we also apply the params
        therefore, the innermost body (the ind tRel) has to throw them away by skipping the params using lambdas
        there are no explicit lambdas to take the non_uni and indices
        instead, we apply them directly to the eta-reduced tRel for call_pos
        *)


        (* ugly but the best alternative *)
        (*
        we need to distinguish the case of a "normal" instance or recursive instance 
        from a nested recursive instance in an augmented argument
        in the last case (the important case) the inner body of an application 
            is of the form containerᵗ args
        we want to apply the functorial lemma
        Therefore, we have to group the parameters into parameter and parameterᵗ
        and for each group add the translated parameterᵗ (which is parameterᵗ but replace typeᵗ with P)
        as well as the functorial property proof which is generated recursively
        *)
        let (body,args) := decompose_app t in
        let res := match body with
        | tInd ind inst =>
            (* check if the functorial lemma is found, if not this might not be the correct argument (for instance argument instead of argumentᵗ) *)
            let lookup_opt := find (fun '(a,_) => eq_inductive ind a) lookup_table in
            if lookup_opt is Some (_,(group_count, lookup)) then
                let args' := (fix f groups xs {struct xs} :=
                    match groups, xs with
                    | S k, a::aᵗ::ys =>
                    (* generate the functorial property *)
                        let fa_opt := create_proof_term param_ctx non_uni_param_ctx indice_ctx ind_pos pred_pos call_pos aᵗ in
                        let fa := 
                            if fa_opt is Some x then
                                x
                            else
                                TemplateToPCUIC.trans empty_env <% I %>
                        in
                        (* let Coq infer the basic instantiations *)
                        hole:: (* a  = type *)
                        hole:: (* aᵗ = translated type *)
                        hole:: (* get_hypothesis param_ctx ind_pos pred_pos aᵗ = replace Tᵗ with P in aᵗ *)
                        fa:: (* recursive proof *)
                        f k ys
                    | _, _ => xs
                    end
                ) group_count args in
                    ret (mkApps lookup args')
                else 
                    None
        | _ => None
        end in
        match res with
        | Some r => Some r
        | None =>
            (* if not nested => relay application *)
            s <- create_proof_term param_ctx non_uni_param_ctx indice_ctx ind_pos pred_pos call_pos a;;
            ret (mkEagerApp s hole)
        end
    | tProd na ty b =>
        (* tProd is important for guarded induction
            removing this case disables guarded induction of the form
            (f: nat -> ind) (IH_f: forall n, P (f n))

            the induction hypothesis should also have all quantification
            but we also need to apply all quantifications to the argument in question
            to get the inductive instance (but we do not have access to the argument directly)

            therefore, we use a few η and β reductions and expansions

            we first compute the hypothesis for the body of the quantification 
            we have to lift the contexts and raise the ind_pos and call_pos to 
                accomodate for the new binder
            we perform eta expansion to explicitely take the argument with a lambda,
            then we apply the quantified argument (the guard of the induction)
                tApp (tRel 1) (tRel 0)
            this application is the new argument for the inner induction hypothesis
            therefore, we apply it to s 
                (which has to be liftet over the eta-expansion but only from 
                    de Bruijn index 1 and higher in order to preserve the binder tProd)
            we use eager application to resolve all intermediately produced lambdas
                a) for a cleaner term
                b) more importantly: to avoid having to specify the types in the 
                    sacrificial tLambda as these are complicated to construct
                    but we also can not use holes when construction the assumption

            for the proofs the quantification tProd is translated to a tLambda
         *)
        let lift_by_1 := lift_context 1 0 in
        s <- create_proof_term
            (lift_by_1 param_ctx) (lift_by_1 non_uni_param_ctx) (lift_by_1 indice_ctx) 
            (S ind_pos) (S pred_pos) (S call_pos) b;;
        let proof_term_body := 
            (* lift for sacrificial lambda *)
            tLambda na hole
                (mkEagerApps 
                (lift 1 1 s) (* lift behind na over sacrificial lambda *)
                [mkApps (tRel 1) [tRel 0]]) in (* arg a *)
        let proof_term_prod := tLambda rAnon (hole) proof_term_body in  (* hole is here not possible but we use eager beta reduction *)
        ret proof_term_prod

    | _ => None
    end
    end.

Definition create_proof_term := create_proof_term_ 100.


(*
augment the arguments in the sense of creating proof terms for each argument
*)
Definition augment_arguments2 (param_ctx non_uni_param_ctx indice_ctx case_ctx xs : context) : list term := 
    let augment_one_arg := 
        fun assumptions i arg =>
            let ind_pos := #|param_ctx|+1+#|non_uni_param_ctx|+i in 
            (* virtual position of the inductive type represented by tRel in the ctor arguments *) 
            (* xs is some mapping of arg_ctx => number of arguments *)
            (* behind all arguments, the instance, indices, and non_uni params 
                keep in mind that the match all arguments are quantified
                and the case is called and instantiation
                therefore, the index of the fixpoint does not depend on which argument is under consideration right now
            *)
            let fix_pos := #|xs|+1+#|indice_ctx|+#|non_uni_param_ctx| in
            let pred_pos := fix_pos + #|case_ctx| in
            (* the proof the induction hypothesis (if one exists) or None otherwise
                (the result is waiting for the argument to be supplied)
            *)
            (* select the ith argument from the constructor arguments
                    due to de Bruijn we need to write N-i-1 to get the ith of N arguments
                we can not influence the order as it is given by the construction of a tCase
                    (but maybe it should stay in correct order to be less confusing in other areas)
            *)
            let arg_off := #|xs| - i - 1 in
            let asm := create_proof_term 
                param_ctx non_uni_param_ctx indice_ctx 
                (ind_pos+arg_off+1) pred_pos fix_pos 
                (lift0 (arg_off+1) arg.(decl_type)) in
            let argument := tRel arg_off in
            let oarg := if asm is (Some asm_body) then
                        (mkEagerApps asm_body [argument])
                        else argument in
            assumptions++[argument]
        in 
    fold_left_i augment_one_arg xs [].

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


Section Principle.

    Variable 
        (inductive:inductive)
        (uinst:Instance.t)
        (mind:mutual_inductive_body)
        (ind:one_inductive_body).

    Definition PropQ := TemplateToPCUIC.trans empty_env <% Prop %>.

    Definition ind_term := tInd inductive uinst.

    (* the kername of the inductive (module path and name) *)
    Definition kn := inductive.(inductive_mind).
    (* environment to lookup the inductive for translation from TemplateCoq to PCUIC *)
    Definition lookup_env := add_global_decl empty_env (kn,InductiveDecl mind).

    (* remember: contexts are reversed
        decompose gives contexts
        it_mk takes contexts
     *)
    (* compute contexts of params, params, non-uniform params, and indices *)
    Definition non_uniform_param_count := 0. (* TODO: guess it correctly *)
    Definition ind_type := ind.(ind_type). (* type of the inductive *)
    Definition ctx_retTy := decompose_prod_assum [] ind_type. (* get params and indices and inner retTy *)
    Definition ctx := ctx_retTy.1.
    Definition retTy := ctx_retTy.2.
        (* for list: ctx=[Type], retTy=Type *)
    Definition indice_ctx := ind_indices ind.
    Definition all_param_ctx := skipn #|indice_ctx| ctx. (* parameters and non-uniform parameter *)
    Definition non_uni_param_ctx := firstn non_uniform_param_count all_param_ctx. (* non-uniform are behind => at the front *)
    Definition param_ctx := skipn #|non_uni_param_ctx| all_param_ctx. 


    (* construct the quantifications in the predicate
       these are all non-uniform parameters, the indices, and 
       an instance of the inductive type instantiated with params and indices
       
       the context has to be liftet directly behind the parameter quantification
       using lift_context [amount] 0 predicate_ctx
       *)
    Definition predicate_ctx := 
        indice_ctx ++ (* quantify over indices *)
        non_uni_param_ctx.
    (*
        in the new induction scheme, we generate an instance oblivious principle
        as the induction is generated on parametric types, we generate a full
        induction scheme (the instance now lies in the indices) but locally viewed
        the instanceᵗ is ignored 
        and the instance needs to be ignored to generate proof terms for functorial instances
        in nested inductive induction hypotheses generated by third-party parametricity translations
    *)
    Definition full_predicate_ctx := 
        let params := map (lift0 (#|non_uni_param_ctx|+#|indice_ctx|)) (mkRels #|param_ctx|)  in
        let non_uni := map (lift0 (#|indice_ctx|)) (mkRels #|non_uni_param_ctx|) in
        let indices := map (lift0 0) (mkRels #|indice_ctx|) in
        let inst_ty := (mkApps ind_term (params ++ non_uni ++ indices)) in
        [vass (rName "instᵗ") inst_ty] ++ predicate_ctx.

    (* use the context to create the predicate type 
        ∀ non-uni indices, Ind params non-uni indices -> ℙ
    *)
    Definition predicate_type := 
        quantify predicate_ctx
        PropQ. (* TODO: correct elimination *)
    (* type of the predicate used in the induction *)

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
    Definition conclusion_type predicateDist :=
        (* [instance] ++ indice_ctx ++ non_uni_param_ctx *)
        let concl_ctx := lift_context (S predicateDist) 0 full_predicate_ctx in
        let predicate := tRel (predicateDist + #|full_predicate_ctx|) in
        (* one lifting is for instanceᵗ *)
        let local_quant_non_uni := map (lift0 (S #|indice_ctx|)) (mkRels #|non_uni_param_ctx|) in
        let local_quant_indices :=  map (lift0 1) (mkRels #|indice_ctx|) in 
                (* ++ [tRel 0] *) (* not needed as the predicate has no instanceᵗ *)
        let concl_ty := mkApps predicate (local_quant_non_uni ++ local_quant_indices) in
        quantify concl_ctx concl_ty.


    (*
    the cases for needed for case analysis/induction

    we map with iteration count to keep track of the de Bruijn indices (distance to predicate)
    reverse is necessary as contexts are in reversed order 
    (the order of the cases does not matter 
        but it is less confusing and nicer to look at when they are in correct order)
    *)

    (* takes argument context (that is given in constructor) in normal view => behind parameters *)
    (* the result is a list **not** a context (=> it is in the correct order as you would write it) *)
    (* let augmented_args mode arg_ctx := 
        (* internal viewpoint: ∀ params P non_uni. • <- here *)
        (*   if this viewpoint is not met, you have to lift the resulting term after using the augmented arguments *)
        (* lift over P behind non_uni parameters *)
        let arg_list := rev (lift_context 1 #|non_uni_param_ctx| arg_ctx) in (* ind is tRel (param+1) the +1 to lift over P *)
        augment_arguments mode param_ctx non_uni_param_ctx indice_ctx arg_list 
    in *)

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
                    (* let arg_ctx := ctor.(cstr_args) in *)
                    (* index instantiation for the conclusion of the ctor 
                        (how to obtain manually: extract of the app from the conclusion of cstr_type) *)
                    (* let ind_list := ctor.(cstr_indices) in *)

                    (* replace floating ind reference (behind params) with inductive type (for arguments) 
                        at position prev. cases + predicate + params
                    *)
                    (* subst [ind_term] (i+1+#|param_ctx|) *)
                    (* lift non-uni params over other cases and over the predicate => directly behind params *)


                    (* correction: cases are now simply the arguments where typeᵗ is replaces with P *)

    Definition generate_hypothesis_type_of_constructor (i: nat) (ctor : constructor_body) : term :=
        (* TODO: or reconstruct manually 
             from cstr_args, cstr_indices, and non_uniform parameters (lift over P before lifting everything over cases)
          *)
          let (all_args,body) := decompose_prod_assum [] ctor.(cstr_type) in
          let ctor_arg_ctx := rev (skipn #|param_ctx| (rev all_args)) in
          let sacr_lam := 
              (* sacrificial lambda to remove param application for the predicate *)
              (* holes are not allowed here but we eagerly perform beta reduction *)
              (* TODO: beta_reduce does not work ? => first reduce then reduce further *)
              (* it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) *)
              (* predicate behind other cases and sacrificial lambdas *)
              sacrificial_lambda (i+1) 0 (i+#|param_ctx|) param_ctx in

          (* replace recursive instance (behind params)
              (the non-uniform are accounted by quantifiers)
              not at i+1+params (liftet over predicate, other cases)
              with predicate behind cases (i)
           *)
(*            beta_reduce *)
          local_subst [sacr_lam] (i+1+#|param_ctx|) 
          (* lift over other cases for correct param access *)
          (lift0 (i+1) (it_mkProd_or_LetIn ctor_arg_ctx body)).


    Definition generate_hypothesis_of_constructor (i: nat) (ctor : constructor_body) : context_decl := 
        let name :=  (rName ("H_"^ctor.(cstr_name))) in
        let H_type := generate_hypothesis_type_of_constructor i ctor in 
        vass name H_type. 

    Definition case_ctx := rev (mapi generate_hypothesis_of_constructor ind.(ind_ctors)).


    (*
    build the context of the type for the induction lemma
    the context contains the parameters, the predicate, and
    all cases (possibly extended with induction hypotheses)

    we do not include the conclusion quantifications here as we view them as 
    a separate section of the induction lemma 
    (this distinction becomes clear in the proof where we build a fixpoint over the
    arguments in the conclusion)
    *)
    Definition lemma_argument_ctx := (* contexts are reversed lists *)
        case_ctx ++
        [vass (rName "P") predicate_type] ++
        param_ctx. (* quantify params *)
     (* all arguments (params, predicate, cases) *)

     (*
     the type of the induction lemma including the conclusion
     ∀ params predicate,                                (* preamble *)
     HCase_1 -> ...                                     (* cases *)
     HCase_n ->
     ∀ non-uni indices (h:Ind params non-uni indices),  (* conclusion *)
       P non-uni indices h
     *)
    Definition type := 
        it_mkProd_or_LetIn lemma_argument_ctx
        (conclusion_type #|case_ctx| ).  (* lift over cases to get to predicate position *)

(* iteration count for managing which case assumption to call *)
Definition generateBranchesInductionPrinciple :=
    let gen_ith_branch :=
        fun i ctor =>
            let arg_ctx := ctor.(cstr_args) in
            {|  Ast.bcontext := (* args is a context (reversed) but we want names in order *)
                    map decl_name (rev arg_ctx) ;
                Ast.bbody := 
                    let aug_args := 
                        let arg_list := rev (lift_context 1 #|non_uni_param_ctx| arg_ctx) in (* ind is tRel (param+1) the +1 to lift over P *)
                        augment_arguments2 param_ctx non_uni_param_ctx indice_ctx case_ctx arg_list 
                    in (* virtually behind ∀ Params P. • *)
                    let branch_i_fun :=
                        Ast.tRel (#|arg_ctx|+#|full_predicate_ctx|+1+
                        (* behind ctor args and fixpoint arguments (non_uni, indices, instance), and f *)
                        (* select the ith case from the assumptions
                            due to de Bruijn we need to write N-i-1 to get the ith of N arguments *)
                                    (#|case_ctx| -i-1)) in (* H_ctor *)
                    let lifted_non_uni_param :=
                        (* lift non_uni over args, instance, indices *)
                        map (Ast.lift0 (#|arg_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) in
                    let branch_i_body := lifted_non_uni_param ++ (map PCUICToTemplate.trans aug_args)
                    in
                    Ast.mkApps branch_i_fun branch_i_body
            |} 
    in
    mapi gen_ith_branch ind.(ind_ctors).


Definition matchInductiveInductionPrinciple :=
    let case_info := {| ci_ind := inductive;
                        ci_npar := #|all_param_ctx|;
                        ci_relevance := Relevant |} in
    let predicate := {| Ast.puinst := uinst;
                        Ast.pparams := 
                            map (Ast.lift0 
                                (* instance, indices, non-uni, f,
                                cases, predicate *)
                                (1+#|indice_ctx|+#|non_uni_param_ctx|+1+#|case_ctx|+1)) 
                                (mkAstRels #|param_ctx|) (* provide param bindings *)
                            ++ 
                                (* instance and indices to reach non-uni in fix point definition *)
                            map (Ast.lift0 (1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|); (* and non-uni param bindings *)
                        Ast.pcontext :=
                                (* names for indice bindings and the match instance (for return type context) *)
                                map (fun _ => rAnon) indice_ctx ++ [rName "inst"];
                                (* there are new binders for the indices and instance in the return type *)
                        Ast.preturn := 
                            (* P holds with non-uni, indices (no instance) *)
                            (* Ast.hole not possible for types without ctors *)
                            let ret_head_type :=
                                (* local instance, indices, fix point arguments (full pred),f  *)
                                Ast.tRel (1+#|indice_ctx|+#|full_predicate_ctx|+1+#|case_ctx|) in
                            let ret_tail_type :=
                                    (* lift over instance, indices, instance (fix), indices (fix) *)
                                    map (Ast.lift0 (1+#|indice_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++
                                    (* lift over instance *)
                                    map (Ast.lift0 1) (mkAstRels #|indice_ctx|) 
                                    (* instance is tRel 0 *)
                            in
                            Ast.mkApps ret_head_type ret_tail_type 
                        |} in 
        let inductive_instance := Ast.tRel 0 in 
        let branches := generateBranchesInductionPrinciple
    in 
    (* match
        TODO: write what we are doing
        the tCase in TemplateCoq is easier than the tCase in PCUIC (too many redundant annotations)
    *)
    Ast.tCase case_info predicate inductive_instance branches.


Definition inductionPrincipleBody :=
                it_mkLambda_or_LetIn 
                (* lift over f (recursive fixpoint function), cases, predicate *)
                (lift_context (1 + #|case_ctx| + 1) 0 full_predicate_ctx)
                (TemplateToPCUIC.trans lookup_env matchInductiveInductionPrinciple).


Definition createInductionPrinciple :=
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
            (* placeholder *)

            tFix [ {|
            dname := rName "f";
            dtype := conclusion_type (#|case_ctx|); (* hole not possible for types without ctors *)
            dbody := inductionPrincipleBody  ; 
            rarg  := #|full_predicate_ctx| - 1 (* the last argument (the instance) is structural recursive *)
            |} ] 0
        )
        )
    )
    Cast
    (PCUICToTemplate.trans type).

End Principle.

End IH.