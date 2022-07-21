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
From MetaCoq.Template Require Import All ReflectAst.

From MetaCoq.Translations Require Import translation_utils.
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

(* From MetaCoq.Translations Require Import param_original. *)
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


(* Definition get_decls (ctx : Env.context) : list BasicAst.aname :=
    fold_left _ _ (fun acc (decl:BasicAst.context_decl term)=> decl.(decl_name) :: acc) [] ctx. *)
    
Fixpoint get_decls (ctx : Env.context ) : list BasicAst.aname :=
    match ctx with
    | nil => nil
    | d :: decls => d.(decl_name) :: get_decls decls
    end.

(* Definition eqb_term t t' : bool :=
    if EqDec_term t t' then false else true. *)
Definition is_same_type t arity i :=
    match t with
    | Ast.tRel n => (n+i+1) == arity
    | _ => false
    end.

Definition fl_ident : ident -> ident :=
    fun id => id ^ "_fl".

Definition get_kn_from_ty ty mp :=
    match ty with
    | Ast.tInd {| inductive_mind := (_, name) |} _ => (mp,fl_ident name)
    | _ => (MPfile [""],"ith type was not an inductive")
    end.
  
Fixpoint generate_ith_arguments (A : Ast.term)(rels : list nat) (argsA : Env.context) (pcontext_size : nat) (TC : tsl_context) mp arity:=
    match rels,argsA with
    | i::is, d :: decls => 
        let ith_ty := d.(decl_type) in 
        let prf := if is_same_type ith_ty arity i
            then Ast.tRel (#|argsA|+i + pcontext_size)
            else let fl_kn := get_kn_from_ty ith_ty mp in
                match (lookup_tsl_table (snd TC) (ConstRef fl_kn)) with
                | Some t => t
                | None => Ast.tVar ("fundamental lemma :" ^ (string_of_kername fl_kn)^"is not available in the translation context")
                end
            in 
        [Ast.tRel i ; Ast.tApp prf [Ast.tRel i]] :: generate_ith_arguments A is decls pcontext_size TC mp arity
    | _, _ => []
    end.

Definition generate_bbody_forall_A_is_A_a uinstA is_Ak (A : Ast.term) (argsA: Env.context) (k : nat) (uinstisA : Instance.t) TC mp arity: Ast.term :=
    let is_K := Ast.tConstruct {| inductive_mind := is_Ak ; inductive_ind := uinstA |} k uinstisA in
    (* TODO HOW TO MERGE UNIVERSES *)
    (* FIXME is this always right? *)
    let pcontext_size := 1 in
    match argsA with
    | nil => is_K
    | _ => 
        (* to reach f we need to know the size of pcontext later will be replaced*)
        let R := flat_map rev (generate_ith_arguments A (seq 0 #|argsA|) argsA pcontext_size TC mp arity) in
        Ast.tApp is_K (rev R)
    end. 

Definition get_ctors (mind : Env.mutual_inductive_body) (uinst : nat) : list Env.constructor_body :=
    match nth_error mind.(Env.ind_bodies) uinst with
    | Some ib => ib.(Env.ind_ctors)
    | None => [] (* how to handle better this case? *)
    end.

Definition generate_branches_forall_A_is_A_a (uinstA : nat) (uinstisA : Instance.t) (A is_A : Ast.term)(Ak is_Ak : kername) (A_mind is_A_mind : Env.mutual_inductive_body) TC mp : list (Ast.branch Ast.term) :=
    let get_one_branch := fun (k:nat) ctorA =>
        let (argsA,arity) := match ctorA with Env.Build_constructor_body _ argsA _ _ arity => (argsA,arity)end in
        let bctx := get_decls argsA in
        let bbdy := generate_bbody_forall_A_is_A_a uinstA is_Ak A argsA k uinstisA TC mp arity in
        {| Ast.bcontext := bctx ; Ast.bbody := bbdy |} 
        in
    mapi get_one_branch (get_ctors A_mind uinstA).

Definition get_inductive_uinst (t : Ast.term) := 
    match t with
    | Ast.tInd i u => (i,u)
    | _ => ({| inductive_mind := (MPfile [""],"error in generate the body of fundamental lemma") ; inductive_ind := 0 |} , [] )
    end.

Definition generate_body_forall_A_is_A_a Ak is_Ak A is_A A_mind is_A_mind TC mp :=
    let (inductiveA,uinstA) := get_inductive_uinst A in 
    let (inductiveisA,uinstisA) := get_inductive_uinst is_A in 
    let case_info := {| ci_ind := inductiveA ; 
                        ci_npar := 0 ; 
                            (* TODO update for nested types *)
                        ci_relevance := Relevant |} in
    let predicate := {| Ast.puinst := uinstA ; 
                        Ast.pparams := []; (* not handling params for the moment *) 
                        Ast.pcontext := [rName "inst"];
                        Ast.preturn := Ast.mkApps is_A [Ast.tRel 0]
                        |} in
    let inductive_instance := Ast.tRel 0 in 
    let branches := generate_branches_forall_A_is_A_a inductiveA.(inductive_ind) uinstisA A is_A Ak is_Ak A_mind is_A_mind TC mp in
    Ast.tLambda (rName "inst") A
    (Ast.tCase case_info predicate inductive_instance branches).

(* Definition forall_A_is_A_a (A : Ast.term) (is_A : Ast.term) : Ast.term := *)
(* forall (A: Type) (P : A -> Set), forall a : A, P a *)    
Definition get_kername (A : Ast.term) : kername :=
    match A with
    | Ast.tInd ({| inductive_mind := k |} ) _ => k
    | _ => (MPfile [""],"lemma body error A was not an inductive")
    end.

Definition tm_debug {A} a s :=
        tmMsg "===============";;
        tmMsg ("===  "^s^ "  ===");;
        tmMsg "===============";;
        a <- tmEval lazy a ;;
        @tmPrint A a;;
        tmMsg ("========== end "^s^ "===============");;
        ret a.


Definition generate_fixpoint A is_A Ak is_Ak A_mind is_A_mind TC mp:=
    let conclusion_type := forall_A_is_A_a_type A is_A in
    let body := generate_body_forall_A_is_A_a Ak is_Ak A is_A A_mind is_A_mind TC mp in
        is_A <- tm_debug is_A "Type is_A";;
        A <- tm_debug A "Type A";;
        conclusion_type <- tm_debug conclusion_type "conclusion Type : forall a : is_A a" ;;
        body <- tm_debug body "Body" ;;
    let mfixpoint := 
        [{|
            dname := rName "f";
            dtype := conclusion_type ; 
            dbody := body  ; 
            rarg  := 0 (* for non container types you just need 1 arg*)   
                     (* for container types you have A : type and is_A : A -> Prop in ctx *)
                     (* for the moment just considering "normal" types *)
         |}] in 
    let fixp_ :=  
(*         (it_mkLambda_or_LetIn 
        [] the context depends on the parameters *)
        (Ast.tFix mfixpoint 0)
        in
        fixp <- tm_debug fixp_ "fixpoint";;
        let decl := {|  Env.cst_universes := is_A_mind.(Env.ind_universes) ;
                        Env.cst_type := conclusion_type; 
                        Env.cst_body := Some fixp;
                        Env.cst_relevance := Relevant |} in (* FIXME is it always relevant? *)
        ret (fixp,decl).

Definition create_T_is_T {T : Type} (x : T)  (TC : tsl_context) : TemplateMonad tsl_context :=
        p <-  tmQuoteRec x ;;
    let (genv,is_A) :=  (p : Env.program) in
    let is_Ak := get_kername is_A in
        is_A_mind <- tmQuoteInductive is_Ak;;
    let A := get_A_from_is_A genv in
    let Ak := get_kername A in
        mp <- tmCurrentModPath tt ;;
        A_mind <- tmQuoteInductive Ak;;
        '(fixp,decl) <- generate_fixpoint A is_A Ak is_Ak A_mind is_A_mind TC mp;;
    let fl_name := fl_ident Ak.2 in
    let fl_kn := (mp,fl_name) in
(*         tmMkDefinition fl_name fixp_decl.1;; *)
        tmMkDefinition fl_name fixp;;
    let Σ' := ((Env.add_global_decl (fst TC) (fl_kn, Env.ConstantDecl decl)),is_A_mind.(Env.ind_universes))  in
    let (_,uinstA) := get_inductive_uinst is_A in 
    let E' := ((ConstRef fl_kn, Ast.tConst fl_kn uinstA) :: (snd TC)) : tsl_table in
        TC' <- tmEval lazy (Σ',E');;
        print_nf (Ak.2 ^ " fundamental lemma has been generated as " ^ fl_name) ;;
    ret TC'.