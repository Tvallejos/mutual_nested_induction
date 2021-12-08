(*
created using github coq-8.13 branch (f000a1d66428370ac98685fb8aaca79c225a91c0)
not opam coq-metacoq 1.0~beta2+8.13
    as the opam version has less useful definitions for inductive types, cases, ...
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
From MetaCoq.PCUIC Require Import PCUICToTemplate.

Definition relevant_binder (n:name) :=
    {|
    binder_name := n;
    binder_relevance := Relevant
    |}.
Definition rAnon := relevant_binder nAnon.
Definition rName n := relevant_binder (nNamed n).

(* Definition hole := TemplateToPCUIC.trans [] hole. *)
(* Definition hole := tEvar fresh_evar_id []. *)

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
Definition AstPlaceholder := Ast.mkApp <% @TODO %> (Ast.hole).
Definition placeholder := TemplateToPCUIC.trans [] AstPlaceholder.

(*
n = destination
k = local binder count

(* we simplify 
does not change binder structure in contrast to normal subst
(but it could without causing problems) *)
Correction: works like subst now
*)
Fixpoint local_subst_ (s:list term) (n:nat) (k:nat) (t:term) := 
  match t with
  | tRel m =>
      (* difference: correct distance is dest (n)+local (k) *)
	  if k+n <=? m
      then
        (* difference: only lift over local binders *)
        if nth_error s (m - k-n) is Some b then lift0 k b else tRel (m - #|s|)
      else tRel m
  | tEvar ev args => tEvar ev (map (local_subst_ s n k) args)
  | tProd na A B => tProd na (local_subst_ s n k A) (local_subst_ s n (S k) B)
  | tLambda na T M => tLambda na (local_subst_ s n k T) (local_subst_ s n (S k) M)
  | tLetIn na b ty b' =>
      tLetIn na (local_subst_ s n k b) (local_subst_ s n k ty) (local_subst_ s n (S k) b')
  | tApp u0 v => tApp (local_subst_ s n k u0) (local_subst_ s n k v)
  | tCase ind p c brs =>
      let p' := map_predicate_k id (local_subst_ s n) k p in
      let brs' := map_branches_k (local_subst_ s n) id k brs in
      tCase ind p' (local_subst_ s n k c) brs'
  | tProj p c => tProj p (local_subst_ s n k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (local_subst_ s n k) (local_subst_ s n k')) mfix in
      tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (local_subst_ s n k) (local_subst_ s n k')) mfix in
      tCoFix mfix' idx
  | _ => t
  end.

Definition local_subst s n := local_subst_ s n 0.




    (* TODO: there once was a function doing this already (was it mkApp in a previous version?) *)
Definition mkEagerApp (a:term) (b:term) : term :=
    match a with 
    (* we completely ignore the type of the lambda as we might eliminate an error or at least do not introduce one *)
    | tLambda na _ body =>
        body {0:=b}
    | _ => tApp a b 
    end.

Fixpoint mkEagerApps (t:term) (us:list term) : term :=
    match us with
    | [] => t
    | u::ur => mkEagerApps (mkEagerApp t u) ur
    end.

    (* Locate "_ { _ := _ }". *)


    (*

    this function takes the type of an arguments, some extra information
    and constructs a proof or type of the induction hypothesis
    both are very similar and share all the structure
    but they are independent and we only need one at a time
    Therefore, the mode toggle switches between generating the 
    induction hypothesis type for the cases (IHAssumption)
    and the proofs in the match when the instantiation for the assumption is needed

    technical detail:
    we design the function with the assumptions in mind and will
    in the de Bruijn indices accordingly
    for the proof construction, we can use holes to compute the correct instantiations and types

    Arguments:
    *_ctx   - the contexts used for size and types in assumptions
    ind_pos - the virtual position of the inductive type in the arguments of the constructor
        the arguments are taken directly from the one_inductive_type (plus a lifting for P)
        with the constructor type
        Ind -> Params -> Non-uni -> Args -> tApp (tRel ...) ...
        and the standard viewpoint ∀ Params P (manually liftet to accomodate P) non-uni, •
        the instantiation should be #|param_ctx|+1+#|non_uni_param_ctx|+i
        where i is the number of the current argument
        to account for lifting in the other arguments
    call_pos - the de Bruijn index of a function to generate the hypothesis/proof
        for assumptions this is the position of P => predicate which is instantiated with the non_uni, indices, and instance
            typically at #|non_uni_param_ctx|+i
            behind the non_uni arguments (which are quantified in the case) and the other arguments
        for proofs this is a proof of P => the fixpoint function f to be called with the (inferred) non_uni, indices and the (structurally smaller) instance
            for a typical proof the fixpoint is behind
                all ctor arguments (keep in mind that the applications to the case take place all at one level behind all arguments => no individual lifting),
                the instance, indices, non_uniform parameters (arguments of the fixpoint)
    t - the type of the ctor

    return value:
    Some u - if induction is possible in this argument, u is returned
        hereby u stands for λ arg. ...
        therefore, to use the assumption/proof, one has to instantiate the result
        with a tRel pointing to the argument for which the assumption/proof is computed
        this argument is then applied to P or the fixpoint (or more generally, to the call_pos as last argument after non_uni and indices)
    None - if no induction is possible or the special kind of induction is not supported
    
    *)


(*
this function 
when called with IHAssumption as mode:
    extends a list of arguments into a list of arguments and their induction hypotheses
        this list can be used to construct a case in and induction lemma
when called with IHProof as mode:
    generated proofs and calls for all arguments and to-be generated induction hypotheses
        in order to give correct instantiations for case in the induction lemma

The argument xs is an argument list => not reversed 
    (but in correct order like you write it in the definition of the constructor)

This function uses a virtual viewpoint: ∀ params P non_uni. • <- here
    the viewpoint is mainly interesting for the assumption generation and is needed
        for a correct instantiation of the arguments
    to reach this viewpoint in the argument list, 
        the context of arguments has to be liftet by 1 (for P) after non_uni parameters
        and then reversed

As we handle induction hypotheses and the proofs all in one place,
this is the only place to adjust the difference induction hypotheses
=> it is possible to toggle between case analysis and induction hypotheses in the function
*)


Definition hole := tEvar fresh_evar_id [].

Section IH.

Variable (lookup_table : list (inductive * (nat * term))).

Definition get_hypothesis param_ctx (ind_pos:nat) (pred_pos:nat) (t:term) :=
    let param_pos := pred_pos + 1 in
    local_subst [
        (* sacrificial lambda to remove param application for the predicate *)
        (* holes are not allowed here but we eagerly perform beta reduction *)
        (* TODO: beta_reduce does not work ? => first reduce then reduce further *)
        (* it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) *)
        it_mkLambda_or_LetIn (lift_context param_pos 0 param_ctx)
        (* it_mkLambda_or_LetIn (lift_context (i+1) 0 param_ctx) *)
        (tRel pred_pos) (* predicate behind other cases and sacrificial lambdas *)
        (* (tRel (i+#|param_ctx|)) *)
        (* ind_term  *)
    ]
    ind_pos
    (* (i+1+#|param_ctx|)  *)
    t
    (* lift over other cases for correct param access *)
    (* (lift0 (i+1)
        (it_mkProd_or_LetIn ctor_arg_ctx body)
    ) *)
    .


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
        (* s <- create_proof_term param_ctx non_uni_param_ctx indice_ctx ind_pos call_pos a;;
        ret (mkEagerApp s hole) *)
        (* alternative: ret (tApp s hole) *)


        (* ugly but the best alternative *)
        let (body,args) := decompose_app t in
        let res := match body with
        | tInd ind inst =>
            (* nested type *)
            let lookup_opt := find (fun '(a,_) => eq_inductive ind a) lookup_table in
            (* let (group_count,lookup) := _ : functorial_instance ind in
            let group_count := lookup_inst.(param_groups) in
            let lookup := lookup_inst.(func_lemma) in *)
            if lookup_opt is Some (_,(group_count, lookup)) then
                (* ret placeholder *)
                (* let lookup := TemplateToPCUIC.trans [] <% listᵗ_func %> in *)
                let args' := (fix f groups xs {struct xs} :=
                    match groups, xs with
                    | S k, a::aᵗ::ys =>
                        let fa_opt := create_proof_term param_ctx non_uni_param_ctx indice_ctx ind_pos pred_pos call_pos aᵗ in
                        let fa := 
                            if fa_opt is Some x then
                                x
                            else
                                (* (λ x y: y) : ∀ (x:X), F x -> F x *)
                                (* tLambda rAnon hole (tLambda rAnon hole (tRel 0)) *)
                                TemplateToPCUIC.trans [] <% I %>
                        in
                        hole:: (* a  = type *)
                        hole:: (* aᵗ = translated type *)
                        hole:: (* get_hypothesis param_ctx ind_pos pred_pos aᵗ = replace Tᵗ with P in aᵗ *)
                        fa:: (* recursive proof *)
                        f k ys
                    | _, _ => xs
                    (* | _, [x] => xs *)
                    (* | _, [] => xs *)
                    (* | _, y::yr => hole::f groups yr *)
                    end
                ) group_count args in
                ret (mkApps lookup args')
                (* None *)
                else 
                    None
        | _ => None
        end in
        match res with
        | Some r => Some r
        | None =>
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
        s <- create_proof_term
            (lift_context 1 0 param_ctx) 
            (lift_context 1 0 non_uni_param_ctx) 
            (lift_context 1 0 indice_ctx) 
            (S ind_pos) (S pred_pos) (S call_pos) b;;
        ret(tLambda rAnon (hole) (* hole is here not possible but we use eager beta reduction *)
        (
            (* lift for sacrificial lambda *)
            (tLambda na hole)
            (mkEagerApps 
            (lift 1 1 s) (* lift behind na over sacrificial lambda *)
            [mkApps (tRel 1) [tRel 0]]) (* arg a *)
        ))

    | _ => None
    end
    end.

Definition create_proof_term := create_proof_term_ 100.


Definition augment_arguments2 (param_ctx non_uni_param_ctx indice_ctx case_ctx:context) (xs:list context_decl) : list (term) := 
    fold_left_i
    (fun assumptions i arg =>
        let ind_pos := #|param_ctx|+1+#|non_uni_param_ctx|+i in (* virtual position of the inductive type represented by tRel in the ctor arguments *) 
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
            let arg_off := #|xs| - i - 1 in
            let asm := create_proof_term 
                param_ctx non_uni_param_ctx indice_ctx 
                (ind_pos+arg_off+1) pred_pos fix_pos 
                (lift0 (arg_off+1) arg.(decl_type)) in
            (* let asm := None in *)
            (* select the ith argument from the constructor arguments
                    due to de Bruijn we need to write N-i-1 to get the ith of N arguments
                we can not influence the order as it is given by the construction of a tCase
                    (but maybe it should stay in correct order to be less confusing in other areas)
            *)
            let argument := tRel arg_off in
            assumptions++[
                if asm is (Some asm_body) then
                    (mkEagerApps asm_body [argument])
                    (* let AstPlaceholder := Ast.mkApp <% @TODO %> (Ast.hole) in
                    let placeholder := TemplateToPCUIC.trans [] AstPlaceholder in
                    placeholder *)
                else
                    argument
                ]
        
            (* let IHs := 
                if asm is (Some asm_body) then
                    (* suplly the body with the argument *)
                    assumptions++[(mkEagerApps asm_body [argument])]
                    (* [] *) (* this results in no induction hypotheses => case analysis *)
                else 
                    (* the argument does not allow for induction *)
                    []
            in

            (* add argument instantiation (tRel) and proof the induction hypothesis (call to f and a bit of stuff around it)
                as application arguments *)
            assumptions++[Argument (vass rAnon argument)]++IHs *)
    )
    xs
    [].



(* adds quantification of context around body *)
Notation quantify:= (it_mkProd_or_LetIn)(only parsing).

(* Definition ind_indices (mind:mutual_inductive_body) (ind:one_inductive_body) := 
    let param_count := mind.(ind_npars) in
    let (param_inds,_) := decompose_prod_assum [] ind.(ind_type) in
    rev (skipn mind.(ind_npars) (rev (param_inds))). *)



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

    Definition PropQ := TemplateToPCUIC.trans [] <% Prop %>.

    Definition ind_term := tInd inductive uinst.

    (* the kername of the inductive (module path and name) *)
    Definition kn := inductive.(inductive_mind).
    (* environment to lookup the inductive for translation from TemplateCoq to PCUIC *)
    Definition lookup_env :global_env := [(
        (kn,InductiveDecl mind)
    )].

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
        [vass (rName "instᵗ") 
            (mkApps ind_term 
            (
                map (lift0 (#|non_uni_param_ctx|+#|indice_ctx|)) (mkRels #|param_ctx|) ++ (* params *)
                map (lift0 (#|indice_ctx|)) (mkRels #|non_uni_param_ctx|) ++ (* non_uni *)
                map (lift0 0) (mkRels #|indice_ctx|) (* indices *)
            ) (* params, non-uni, and indices*)
            )] ++ 
            predicate_ctx.

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
        (quantify
           (lift_context (S predicateDist) 0 full_predicate_ctx) (* [instance] ++ indice_ctx ++ non_uni_param_ctx *)
        (mkApps 
            (tRel (predicateDist + #|full_predicate_ctx|)) (* tRel to predicate *)
            (
                (* one lifting is for instanceᵗ *)
                map (lift0 (S #|indice_ctx|)) (mkRels #|non_uni_param_ctx|) ++ (* apply locally quant. non-uniform *)
                map (lift0 1) (mkRels #|indice_ctx|) (* apply locally quant. indices *)
                (* ++ [tRel 0] *) (* not needed as the predicate has no instanceᵗ *)
            )
        )).


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


    Definition case_ctx :=
        (rev(
            mapi (fun i ctor => 
                vass (rName ("H_"^ctor.(cstr_name))) 
                    (
                        (* TODO: or reconstruct manually 
                            from cstr_args, cstr_indices, and non_uniform parameters (lift over P before lifting everything over cases)
                        *)
                        let (all_args,body) := decompose_prod_assum [] ctor.(cstr_type) in
                        let ctor_arg_ctx := rev (skipn #|param_ctx| (rev all_args)) in

                        (* replace recursive instance (behind params)
                            (the non-uniform are accounted by quantifiers)
                            not at i+1+params (liftet over predicate, other cases)
                            with predicate behind cases (i)
                         *)
                         (* beta_reduce( *)
                        local_subst [
                            (* sacrificial lambda to remove param application for the predicate *)
                            (* holes are not allowed here but we eagerly perform beta reduction *)
                            (* TODO: beta_reduce does not work ? => first reduce then reduce further *)
                            (* it_mkLambda_or_LetIn (map_context (fun _ => hole) param_ctx) *)
                            it_mkLambda_or_LetIn (lift_context (i+1) 0 param_ctx)
                            (tRel (i+#|param_ctx|)) (* predicate behind other cases and sacrificial lambdas *)
                            (* ind_term  *)
                        ]
                        (i+1+#|param_ctx|) 
                        (* lift over other cases for correct param access *)
                        (lift0 (i+1)
                            (it_mkProd_or_LetIn ctor_arg_ctx body)
                        )
                        (* ) *)
                    )
                    (* ctor.(cstr_type) *)
            ) ind.(ind_ctors)
        )).


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
            dbody := 
                it_mkLambda_or_LetIn 
                (* lift over f (recursive fixpoint function), cases, predicate *)
                (lift_context (1 + #|case_ctx| + 1) 0 full_predicate_ctx)

                (* match
                    TODO: write what we are doing
                    the tCase in TemplateCoq is easier than the tCase in PCUIC (too many redundant annotations)
                *)
                (* placeholder *)
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
                                (mkAstRels #|param_ctx|) ++ (* provide param bindings *)
                            (* instance and indices to reach non-uni in fix point definition *)
                            map (Ast.lift0 (1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) (* and non-uni param bindings *)
                        ;
                        Ast.pcontext :=
                            (* names for indice bindings and the match instance (for return type context) *)
                            map (fun _ => rAnon) indice_ctx ++
                            [rName "inst"];
                            (* there are new binders for the indices and instance in the return type *)
                        Ast.preturn := 
                        (* P holds with non-uni, indices (no instance) *)
                        (* Ast.hole not possible for types without ctors *)
                        Ast.mkApps 
                        (* local instance, indices, fix point arguments (full pred),f  *)
                        (Ast.tRel (1+#|indice_ctx|+#|full_predicate_ctx|+1+#|case_ctx|))
                        (
                            (* lift over instance, indices, instance (fix), indices (fix) *)
                            map (Ast.lift0 (1+#|indice_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++
                            (* lift over instance *)
                            map (Ast.lift0 1) (mkAstRels #|indice_ctx|) 
                            (* instance *)
                            (* [Ast.tRel 0] *)
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
                                if false then (* TODO: remove *)
                                        AstPlaceholder
                                else


                                        let aug_args := 
                                            let arg_list := rev (lift_context 1 #|non_uni_param_ctx| arg_ctx) in (* ind is tRel (param+1) the +1 to lift over P *)
                                            augment_arguments2 param_ctx non_uni_param_ctx indice_ctx case_ctx arg_list 
                                        in (* virtually behind ∀ Params P. • *)




                                        Ast.mkApps
                                        (Ast.tRel (#|arg_ctx|+#|full_predicate_ctx|+1+
                                        (* behind ctor args and fixpoint arguments (non_uni, indices, instance), and f *)
                                        (* select the ith case from the assumptions
                                             due to de Bruijn we need to write N-i-1 to get the ith of N arguments *)
                                                    (#|case_ctx| -i-1))) (* H_ctor *)
                                        (

                                            (* lift non_uni over args, instance, indices *)
                                            map (Ast.lift0 (#|arg_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                            ( 
                                                map PCUICToTemplate.trans aug_args
                                                (* map (fun a =>
                                                    PCUICToTemplate.trans match a with
                                                    | Argument x | IH x => x.(decl_type)
                                                    end
                                                ) (aug_args) *)
                                                (* or mkRels *)
                                                (* mapi (fun i a =>



                                                    (* match a.(decl_type) with 
                                                    | tRel _ => AstPlaceholder
                                                    | tInd _ _ => AstPlaceholder
                                                    | tConst _ _ => AstPlaceholder
                                                    | _ => Ast.tRel (#|arg_ctx| -i-1)
                                                    end *)
                                                    Ast.tRel (#|arg_ctx| -i-1)
                                                        (* Ast.tRel (#|arg_ctx| -i-1) *)
                                        (* AstPlaceholder *)
                                                ) (rev arg_ctx) *)
                                            )

                                        )


                                    (* (
                                        (*
                                        #|arg_ctx| = number of arguments of the ctor
                                        #|predicate_ctx| = inst+indices+non-uni (arguments of f)
                                        *)

                                        (* if true then
                                        AstPlaceholder
                                        else  *)

                                        (* the proofs generated during augmentation of the arguments *)
                                        let aug_args := augmented_args IHProof arg_ctx in (* virtually behind ∀ Params P. • *)

                                        (* build the proof of the shape 
                                            H_ctor non_uni arg1 IH_1 arg2 IH_2 ...
                                         *)
                                        Ast.mkApps
                                        (Ast.tRel (#|arg_ctx|+#|predicate_ctx|+1+
                                        (* behind ctor args and fixpoint arguments (non_uni, indices, instance), and f *)
                                        (* select the ith case from the assumptions
                                             due to de Bruijn we need to write N-i-1 to get the ith of N arguments *)
                                                    (#|case_ctx| -i-1))) (* H_ctor *)
                                        (
                                            (* the non-uni params are quantified in the fixpoint as arguments
                                                fill them in by lifting the de Bruijn indices over the ctor arguments, the instance, and the indices
                                             *)
                                            map (Ast.lift0 (#|arg_ctx|+1+#|indice_ctx|)) (mkAstRels #|non_uni_param_ctx|) ++ (* non-uni *)
                                            ( (* args and IH proofs *)
                                            (* the correct argument indices and the corresponding proofs 
                                                are calculated directly from the arguments during augmentation
                                                this way, one does not have to keep a rolling iterator for the current argument
                                                    and avoids to reconstruct all information about the induction hypothesis
                                                    (and everything stays at one place)
                                                
                                                here, this procedure results in a simple unwrapping of the proofs
                                             *)
                                                map (fun a =>
                                                    PCUICToTemplate.trans match a with
                                                    | Argument x | IH x => x.(decl_type)
                                                    end
                                                ) (aug_args)
                                            )
                                        )

                                    ) *)
                                ;
                                |}
                            ) ind.(ind_ctors)
                        )
                    )
                ) 
                )
            ; 
            rarg  := #|full_predicate_ctx| - 1 (* the last argument (the instance) is structural recursive *)
            |} ] 0
        )
        )
    )
    Cast
    (PCUICToTemplate.trans type).

End Principle.

End IH.