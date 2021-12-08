
MetaCoq Run (
    (* t <- tmQuote (listᵗ);; *)
    t <- tmQuote (vecᵗ);;
    (* t <- tmQuote (conᵗ);; *)
    (* t <- tmQuote (roseAᵗ);; *)

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
        (* lemma <- tmEval lazy (functorial inductive uinst mind t);; *)
        type <- tmEval lazy (functorial_type inductive uinst t);;
        tt <- tmUnquoteTyped Type type;;
         tmPrint type;; (* this can not be read *)
         lemma <- tmLemma "test" (tt:Type);;
         tmPrint lemma
        (* lemma <- tmEval lazy (functorial inductive uinst t);;
         tmPrint lemma;; (* this can not be read *)
         tmMkDefinition "test" lemma *)
    | [] => tmFail "no inductive body found"
    | _ => tmFail "too many inductive bodies (currently, mutual induction is not supported)"
    end
    | Ast.tApp t _ => f t (* resolve partial evar application *)
    | _ => tmFail "Not an inductive type, maybe try @ind for implicit arguments"
    end) t
).
Print test.