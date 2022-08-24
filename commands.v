(*
commands to execute the programs
one command to register a container
and another one to generate an induction principle
*)

From MetaCoq.Induction Require Import 
    induction
    functorial 
    functorial_lookup
    fundamental_lemma.
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


Definition create_T_is_T {T : Type} (x : T)  (TC : tsl_context) : TemplateMonad tsl_context :=
        p <-  tmQuoteRec x ;;
    let (genv,is_A) :=  (p : Env.program) in
    let is_Ak := get_kername is_A in
        is_A_mind <- tmQuoteInductive is_Ak;;
        is_A <- tm_debug is_A "Type is_A";;
    let A := get_A_from_is_A genv in
        A <- tm_debug A "Type A";;
    let Ak := get_kername (drop_apps A) in
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