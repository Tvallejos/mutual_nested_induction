
From MetaCoq.Template Require Import All ReflectAst.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Induction Require Import util.
Require Import String List.
Import ListNotations Nat.
Import MCMonadNotation.

Local Open Scope bs_scope.
Require Import util.
Print Ast.tInd.

Fixpoint drop_apps t : Ast.term :=
    match t with
    | Ast.tApp t u => drop_apps t
    | Ast.tInd _ _ => t
    | _ => tVar "error drop apps"
    end.

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

Definition conclusion (A is_A : Ast.term) : Ast.term :=
    Ast.tProd (rName "aname") A 
            (Ast.tApp is_A [Ast.tRel 0]).

Definition forall_A_is_A_a_type (conclusion : Ast.term) (ctx : Env.context) : Ast.term :=
    it_mkLambda_or_LetIn ctx conclusion.
(*     match ctx with
    | nil => conclusion
    | cons d td => Ast.tProd (decl_name d) (decl_type d) (forall_A_is_A_a_type conclusion td)
(*     | cons { decl_name := aname, decl_type := ty } td => Ast.tProd aname ty (forall_A_is_A_a_type conclusion) *)
    end. *)



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
    fun id => (id ++ "_fl").

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
                | None => Ast.tVar ("fundamental lemma :" ++ (string_of_kername fl_kn) ++ "is not available in the translation context")
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
        let R := flat_map (@rev _) (generate_ith_arguments A (seq 0 #|argsA|) argsA pcontext_size TC mp arity) in
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
                        ci_npar := #|(ind_params A_mind)| ; 
                            (* TODO update for nested types *)
                        ci_relevance := Relevant    
                            (* this should be the relevance of the i'th body 
                                where i is the instance of the inductive *)|} in
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
        tmMsg ("===  "++s++ "  ===");;
        tmMsg "===============";;
        a <- tmEval lazy a ;;
        @tmPrint A a;;
        tmMsg ("========== end "++s++ "===============");;
        ret a.

    (*
    given an argument Aᵗ generates a function which introduces 
    every needed argument for the predicate to land in type (Aᵗ args)
    for Sort, generate Aᵗ args
    for Product, copy the binder and remember to apply the arguments
    Otherwise generate True

    x is Aᵗ
    t is the type of x
    meant to be called with args as empty list
     *)
    Fixpoint fl_prop (x : Ast.term) (args : list Ast.term) (t : Ast.term) : Ast.term :=
        match t with
        | Ast.tSort univ => 
            Ast.tApp x args
        | Ast.tProd na a b =>
            Ast.tProd na a (
                fl_prop (lift0 1 x) (map (lift0 1) args ++ [Ast.tRel 0]) b
            )
        | _ => PCUICToTemplate.trans TrueQ
        end.
    
    Definition name_from_param (A : context_decl) : aname :=
        let (ana,_,_) := A in 
        let na := match binder_name ana with
                  | BasicAst.nNamed id => BasicAst.nNamed (id ++ "H")
                  | nAnon => BasicAst.nNamed "error name_from_param: parameter should have a name"
                  end in
        mkBindAnn na (binder_relevance ana).



    (* 
    given the parameters and indexes of Aᵗ it generates a new context
    where it adds BH : forall b : B, Bᵗ b for every pair B Bᵗ happening in the parameters
    Meant to be called with reversed contexts *)
    Fixpoint add_AH (params inds: Env.context) (arg1  : list nat) :=
        match params with
        | x::xᵗ::xr => 
            let '((n,arg1), aug_args) := 
                add_AH xr inds
                    (map (fun x => x+3) arg1++[3;2]) in 
                ((S n, arg1),
                    x::xᵗ::
                    (vass (name_from_param x) (fl_prop (tRel 0) [] (lift0 1 xᵗ.(decl_type)))) :: 
                    (mapi (fun i a => map_decl (lift 1 i) a) aug_args))
        | _ => 
        ((0,
            (app_arg_list (#|params|+#|inds|) arg1)),(app params inds))
        end.

Fixpoint drop_parametricity_params_  {A: Type} l : bool -> list A :=
    fun b =>
    match l with
    | nil => []
    | cons h t => if b then drop_parametricity_params_ t (negb b) 
                 else h :: drop_parametricity_params_ t (negb b) 
    end. 

Definition drop_parametricity_params {A:Type} l : list A :=
    drop_parametricity_params_ l true.

Definition change_is_A_args t args : Ast.term :=
    match t with
    | Ast.tApp t u => Ast.tApp t args
    | _ => t
    end.

Definition generate_fixpoint A is_A Ak is_Ak A_mind is_A_mind TC mp:=
    let '((n,args),params) := add_AH (rev (ind_params is_A_mind)) [] [] in (* FIXME WHEN ADDING INDICES *)
    let argrels := map (fun n => Ast.tRel n) args in
    let lifted_A := (change_is_A_args A (drop_parametricity_params argrels)) in
(*     (change_is_A_args is_A argrels) in *)
    let conclusion_type := tProd (rName "aname") lifted_A 
                    (mkApps is_A (argrels++[Ast.tRel 0])) in
(*         body <- tm_debug input "Conclusion type" ;; *)
(*     let conclusion_type := forall_A_is_A_a_type input (rev params) in  *)
        conclusion_type <- tm_debug conclusion_type "conclusion Type : forall a : is_A a" ;;
    let body := generate_body_forall_A_is_A_a Ak is_Ak (drop_apps A) is_A A_mind is_A_mind TC mp (* (n + #|params|) *) in
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
