fun mk_simp_ctxt ctxt =
  (put_simpset HOL_ss ctxt) addsimps Named_Theorems.get ctxt @{named_theorems leon_unfold}

fun prove_tac ctxt =
  HEADGOAL
    (SELECT_GOAL (TRY (auto_tac ctxt)) THEN_ALL_NEW
      (FIRST'
        [Cooper.tac false [] [] ctxt,
         Sledgehammer_Tactics.sledgehammer_with_metis_tac ctxt [] Sledgehammer_Fact.no_fact_override []]))

fun equiv_tac rule ctxt =
  let
    val solve_tac =
      TRY (ALLGOALS (REPEAT_ALL_NEW (resolve_tac ctxt @{thms ext}))) THEN
        Local_Defs.unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems leon_unfold}) THEN
        auto_tac ctxt

    fun ext_tac 0 _ = all_tac
      | ext_tac n k = resolve_tac ctxt @{thms ext} k THEN ext_tac (n - 1) k

    fun induct rule = CSUBGOAL (fn (concl, n) =>
      let
        val (p, args) = strip_comb (HOLogic.dest_Trueprop (Thm.concl_of rule))

        val p_inst = Thm.term_of concl
          |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
          |> apply2 (rpair (map Bound (length args - 1 downto 0)))
          |> apply2 list_comb
          |> HOLogic.mk_eq
          |> fold (fn _ => fn t => Abs ("x", dummyT, t)) (1 upto length args)
          |> Syntax.check_term ctxt
          |> Thm.cterm_of ctxt

        val insts = [(Thm.cterm_of ctxt p, p_inst)]
        val rule = Drule.cterm_instantiate insts rule
      in ext_tac (length args) n THEN resolve_tac ctxt [rule] n end)

    val maybe_induct =
      case rule of
        NONE => K all_tac
      | SOME rule => induct rule
  in
    HEADGOAL maybe_induct THEN solve_tac
  end

fun method_tac pos src = Subgoal.FOCUS (fn {context = ctxt, concl, ...} =>
  let
    val scan = Scan.finite Token.stopper Method.parse;
    val ((m, _), []) =
      src
      |> Token.explode (Thy_Header.get_keywords (Proof_Context.theory_of ctxt)) pos
      |> filter_out Token.is_space
      |> Scan.catch scan
    val state =
      Proof.theorem NONE (K I) [[(Thm.term_of concl, [])]] ctxt
      |> Proof.refine m
      |> Seq.hd
    val {goal, ...} = Proof.simple_goal state
  in
    HEADGOAL (resolve_tac ctxt [Goal.conclude goal])
  end)

fun pat_completeness_auto_tac ctxt =
  Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

fun termination_tac ctxt =
  Function_Common.termination_prover_tac ctxt