



(* Load test_types. *)
(* Load param_test. *)
MetaCoq Run (
    (* t <- tmQuote (nat);; *)
    (* t <- tmQuote (list);; *)
    (* t <- tmQuote (@Vector.t);; *)

    (* t <- tmQuote (paramTest);; *)
    (* t <- tmQuote (indexTest);; *)
    (* t <- tmQuote (depTest);; *)
    (* t <- tmQuote (implicitTest);; *)

        (* needs non uni manually set to 1 *)
    (* t <- tmQuote (nonUniTest);; *)
    (* t <- tmQuote (nonUniDepTest);; *)

    (* t <- tmQuote (boolᵗ);; *)
    (* t <- tmQuote (natᵗ);; *)
    (* t <- tmQuote (listᵗ);; *)
    (* t <- tmQuote (vecᵗ);; *)
    (* t <- tmQuote (roseᵗ);; *)
    (* t <- tmQuote (roseSAᵗ);; *)
    (* t <- tmQuote (roseAᵗ);; *)
    (* t <- tmQuote (dNestᵗ);; *)
    (* t <- tmQuote (dNestLᵗ);; *)
    (* t <- tmQuote (noRoseᵗ);; *)

    t <- tmQuote (roseConᵗ);;
    (* t <- tmQuote (roseRoseᵗ);; *)
    (* t <- tmQuote (guardTestᵗ);; *)
        (* needs non uni manually set to 2 *)
    (* t <- tmQuote (nonUniDepTestᵗ);; *)

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