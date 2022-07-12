(*
commands to execute the programs
one command to register a container
and another one to generate an induction principle
*)

From MetaCoq.Induction Require Import 
    induction
    functorial 
    functorial_lookup.
Require Import functorial.
Require Import functorial_lookup.
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

Definition empty_env := PCUICProgram.build_global_env_map {| universes := ContextSet.empty ; declarations := [] |}.
(*
extracts inductive, mutual_inductive_body, one_inductive_body and universe instance
and applies a given program function
*)
Definition fun_on_ind g (verbose:bool) {T} (rt:T) :=
    t <- tmQuote (rt);;
    (fix f t := match t with
    Ast.tInd ({| inductive_mind := k |} as inductive) uinst => 
    mind <- tmQuoteInductive k;;
    match Env.ind_bodies mind with 
    | [oind] => 
        let mindPC := TemplateToPCUIC.trans_minductive_body empty_env mind in
        let oindPC := TemplateToPCUIC.trans_one_ind_body empty_env oind in
        mindPCred <- tmEval lazy mindPC;;
        oindPCred <- tmEval lazy oindPC;;
        (if verbose then
         tmMsg "==============";;
         tmMsg "===Ind term===";;
         tmMsg "==============";;
         tmPrint (tInd inductive uinst);;
         tmMsg "==============";;
         tmMsg "===Ind type===";;
         tmMsg "==============";;
         tmPrint oindPCred
        else
         ret tt);;
        (g inductive uinst mindPC oindPCred:TemplateMonad unit)
    | [] => tmFail "no inductive body found"
(*     | oind :: oinds => 
        let mindPC := TemplateToPCUIC.trans_minductive_body empty_env mind in
        let oindPC := TemplateToPCUIC.trans_one_ind_body empty_env oind in
        mindPCred <- tmEval lazy mindPC;;
        oindPCred <- tmEval lazy oindPC;;
        (if verbose then
         tmMsg "==============";;
         tmMsg "===Ind term===";;
         tmMsg "==============";;
         tmPrint (tInd inductive uinst);;
         tmMsg "==============";;
         tmMsg "===Ind type===";;
         tmMsg "==============";;
         tmPrint oindPCred
        else
         ret tt);;
        (g inductive uinst mindPC oindPCred:TemplateMonad unit) *)
    | _ => tmFail "too many inductive bodies (currently, mutual induction is not supported)"
    end
    | Ast.tApp t _ => f t (* resolve partial evar application *)
    | _ => tmFail "Not an inductive type, maybe try @ind for implicit arguments"
    end) t.

    (*
    generates an induction principle
    *)
Definition createIH (verbose:bool) {T} rt:=
    @fun_on_ind (
        fun inductive uinst mind t =>
        let inds := collect_tInd t in
        lookup_tbl <- lookup_table inds;;
        lemma <- tmEval lazy (createInductionPrinciple lookup_tbl inductive uinst mind t);;
        (if verbose then
         tmMsg "===============";;
         tmMsg "===  Lemma  ===";;
         tmMsg "===============";;
         tmPrint lemma (* this can not be read *)
        else
          ret tt);;
          let name := t.(ind_name)^"_nested_ind" in
         tmMkDefinition name lemma;;
        tmMsg ("Created "^name)
    ) verbose T rt.


    (*
    creates a functorial lemma type
    and open an obligation for the lemma (and maybe solves it already)
    *)
Definition createFunctorial (verbose:bool) {T} rt:=
    @fun_on_ind (
        fun inductive uinst mind t =>

        type_ <- tmEval lazy (functorial_type_groups inductive uinst t);;
        let (groups,type) := type_:nat * Ast.term in
        (if verbose then
         tmMsg "===============";;
         tmMsg "===  Funct  ===";;
         tmMsg "===============";;
         tmPrint type (* this can not be read *)
        else
          ret tt);;
         ttt <- (tmUnquoteTyped Type type);;
         let lemma_name := t.(ind_name)^"_func" in
         lemma <- tmLemma lemma_name (ttt:Type);;
         (* tmPrint lemma *)
        tmMsg ("Generated "^lemma_name);;
         lemmaQ <- tmQuote lemma;;
         let name := t.(ind_name)^"_func_inst" in
         let inst := 
            {| param_groups := groups; 
                func_lemma := TemplateToPCUIC.trans empty_env lemmaQ |}
            :functorial_instance inductive in
        tmDefinition name inst;;
        tmExistingInstance (VarRef name);;
        tmMsg ("Created "^name)
    ) verbose T rt.

Axiom todo : forall t, t.

Definition get_A_from_is_A (c : Env.global_env) : Ast.term :=
    match c with
    | Env.Build_global_env _ ( d :: decls)  => 
        match d with
        | (_,(Env.ConstantDecl _)) => Ast.tVar "error get_A_from_is_A first declaration not an inductive"
        | (_,(Env.InductiveDecl {| Env.ind_bodies := bodies |})) => 
            match bodies with
            | [ {| Env.ind_indices := indices |} ] => 
                match indices with
                | [ idx ] => 
                    match idx with
                    | mkdecl _ _ A_type => A_type
                    end
                | _ => Ast.tVar "error get_A_from_is_A the body of the inductive declaration should have just one indice"
                end
            | _ => Ast.tVar "error get_A_from_is_A the body of the inductive declaration should have just one inductive body"
            end
        end
    | Env.Build_global_env _ _  => Ast.tVar "error get_A_from_is_A"
    end.

Definition forall_A_is_A_a_type (A is_A : Ast.term) : Ast.term :=
    Ast.tProd (mkBindAnn (nNamed "aname") Relevant) A (Ast.tApp is_A [Ast.tRel 0]).


Definition generate_body_forall_A_is_A_a (A is_A : Ast.term) : Ast.term :=
    let (inductive,uinst) := 
        match A with
        | Ast.tInd inductive uinst => (inductive,uinst)
        | _ => ({| inductive_mind := (MPfile [""],"lemma body error A was not an inductive") ; inductive_ind := 0|}, [])
        end 
(*         : (Kernames.inductive * Instance.t) *)
    in
    let case_info := {| ci_ind := inductive ; 
                        ci_npar := 1 ; (* TODO update for nested types *)
                        ci_relevance := Relevant |} in
    let predicate := {| Ast.puinst := uinst ; 
                        Ast.pparams := []; (* not sure about this one *) 
                        Ast.pcontext := [rName "inst"];
                        Ast.preturn := Ast.mkApps is_A [Ast.tRel 0]
                        |} in
    let inductive_instance := Ast.tRel 0 in 
    let branches := todo _ in
    Ast.tLambda {| binder_name := BasicAst.nNamed "inst" ; binder_relevance := Relevant |} A
    (Ast.tCase case_info predicate inductive_instance branches).

    (* Definition forall_A_is_A_a (A : Ast.term) (is_A : Ast.term) : Ast.term :=
 *)
(* forall (A: Type) (P : A -> Set), forall a : A, P a *)    
Definition create_T_is_T {T : Type} (x : T) : TemplateMonad unit :=
    p <-  tmQuoteRec x ;;
    let (genv,is_A) :=  (p : Env.program) in
    let A := get_A_from_is_A genv in
    let conclusion_type := forall_A_is_A_a_type A is_A in
    let body := generate_body_forall_A_is_A_a A is_A in
    ret tt.
(* tFix [ {|
            dname := rName "f";
            dtype := conclusion_type ; 
            dbody := body  ; 
            rarg  := 1 (* for non container types you just need 1 arg*)   
                     (* for container types you have A : type and is_A : A -> Prop in ctx *)
                     (* for the moment just considering "normal" types *)
            
            |} ] 0 *)
(*  let Σ := TemplateToPCUIC.trans_global (genv,Monomorphic_ctx) : PCUICProgram.global_env_ext_map in 
    let sig := PCUICProgram.global_env_ext_map_global_env_map Σ in *)

  
