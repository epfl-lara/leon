fun map_result_exn _ (Exn.Res r) = Exn.Res r
  | map_result_exn f (Exn.Exn exn) = Exn.Exn (f exn)

fun print_position pos =
  let
    val print_file = Path.implode o Path.base o Path.explode
  in
    case (Position.file_of pos, Position.line_of pos) of
      (SOME file, SOME line) => print_file file ^ ":" ^ Markup.print_int line
    | (SOME file, NONE) => print_file file
    | _ => "<unknown>"
  end

exception Unsupported of string
exception Construction of string * exn
exception Impossible of string
exception Invalid_State of string
exception Timeout of string

local
  fun format_message msg pos = msg ^ " (at " ^ print_position pos ^ ")"
in

fun impossible msg pos =
  raise Impossible (format_message msg pos)

fun invalid_state msg pos =
  raise Invalid_State (format_message msg pos)

fun the_error msg pos NONE = impossible ("expected SOME: " ^ msg) pos
  | the_error _   _   (SOME x) = x

fun single_error _   _   [t] = t
  | single_error msg pos _ = impossible ("expected singleton list: " ^ msg) pos

end

fun print_exn (exn: exn) =
  YXML.content_of (@{make_string} exn)

fun check true _ = ()
  | check false f = error (f ())

fun dupl x = (x, x)

val unvarify_typ =
  let
    fun aux (TVar ((name, idx), sort)) = TFree (name ^ Markup.print_int idx, sort)
      | aux t = t
  in map_atyps aux end

val unvarify =
  let
    fun aux (Var ((name, idx), typ)) = Free (name ^ Markup.print_int idx, typ)
      | aux t = t
  in map_aterms aux o map_types unvarify_typ end

fun print_term ctxt =
  let
    val ctxt' = Config.put show_markup false ctxt
  in YXML.content_of o Syntax.string_of_term ctxt' o unvarify end

fun print_typ ctxt =
  let
    val ctxt' = Config.put show_markup false ctxt
  in YXML.content_of o Syntax.string_of_typ ctxt' o unvarify_typ end

fun print_thm ctxt thm =
  let
    val t = Thm.prop_of thm
    val {oracle, ...} = Thm.peek_status thm
    val suffix = if oracle then " [!]" else ""
  in
    print_term ctxt t ^ suffix
  end

fun all_consts (Const (name, typ)) = [(name, typ)]
  | all_consts (t $ u) = all_consts t @ all_consts u
  | all_consts (Abs (_, _, t)) = all_consts t
  | all_consts _ = []

fun all_frees (Free (name, typ)) = [(name, typ)]
  | all_frees (t $ u) = all_frees t @ all_frees u
  | all_frees (Abs (_, _, t)) = all_frees t
  | all_frees _ = []

fun all_undeclared_frees ctxt =
  all_frees
  #> distinct op =
  #> filter (not o Variable.is_declared ctxt o fst)

fun register_terms ts lthy =
  let
    val ts' = Syntax.check_terms lthy ts |> map HOLogic.mk_Trueprop
    val frees = distinct op = (maps (all_undeclared_frees lthy) ts')
    val (free_names', lthy) = Variable.add_fixes (map fst frees) lthy
    val frees' = map Free (free_names' ~~ map snd frees)
    val frees = map Free frees
    val ts'' = map (subst_free (frees ~~ frees')) ts'
  in
    (ts'', fold Variable.declare_term ts'' lthy)
  end

fun qualify ctxt name =
  Context.theory_name (Proof_Context.theory_of ctxt) ^ "." ^ name

fun compute_sccs nodes edges =
  Graph.empty
  |> fold Graph.new_node nodes
  |> fold (fn edge => perhaps (try (Graph.add_edge edge))) edges
  |> (fn graph => map (map (Graph.get_node graph)) (Graph.strong_conn graph))
  |> rev

val dummify_types = map_types (K dummyT)

fun fold_opt _ [] y = SOME y
  | fold_opt f (x :: xs) y = Option.mapPartial (fold_opt f xs) (f x y)

fun fold_res _ [] y = Exn.Res y
  | fold_res f (x :: xs) y = Exn.maps_result (fold_res f xs) (f x y)

fun map_generalized f t =
  case t of
    Const (@{const_name Pure.all}, typ) $ Abs (name, typ', t) =>
      (Const (@{const_name Pure.all}, typ) $ Abs (name, typ', map_generalized f t))
  | _ =>
      f t

fun mk_untyped_eq (x, y) =
  HOLogic.eq_const dummyT $ x $ y

fun strip_first_prem t =
  let
    val prems = tl (Logic.strip_imp_prems t)
    val concl = Logic.strip_imp_concl t
  in Logic.list_implies (prems, concl) end

fun map_prems f t =
  let
    val prems = Logic.strip_imp_prems t
    val concl = Logic.strip_imp_concl t
  in Logic.list_implies (map f prems, concl) end

fun mk_induction_schema lthy thms =
  let
    val props = map (unvarify o Thm.prop_of) thms

    val ((heads, argss), rhss) =
      props
      |> map (HOLogic.dest_eq o HOLogic.dest_Trueprop)
      |> split_list
      |>> map strip_comb |>> split_list

    val names =
      map (fst o dest_Const) heads
      |> distinct op =
      |> Name.invent_names (Variable.names_of (fold Variable.declare_names (flat argss) lthy)) "temp"
      |> map swap

    fun subst (t as Const (name, _)) =
         (case AList.lookup op = names name of SOME new => Free (new, dummyT) | NONE => t)
      | subst t = t

    fun mk_prop head args rhs =
      map_aterms subst rhs
      |> pair (list_comb (subst head, args))
      |> mk_untyped_eq
      |> HOLogic.mk_Trueprop

    fun mk_head name = (Binding.name name, NONE, NoSyn)
    val props = map (pair (Binding.empty, [])) (Syntax.check_terms lthy (@{map 3} mk_prop heads argss rhss))
    val heads = map (mk_head o snd) names

    val (info, _) =
      (* FIXME funny warning *)
      Function.add_function heads props Function_Common.default_config pat_completeness_auto_tac lthy

    val raw_prop = unvarify (Thm.prop_of (hd (#pinducts info)))
    val prop = map_prems (map_generalized strip_first_prem) (strip_first_prem raw_prop)
    val frees = distinct op = (map fst (all_frees prop))

    fun tac ctxt =
      Induction_Schema.induction_schema_tac ctxt [] THEN
        HEADGOAL (Pat_Completeness.pat_completeness_tac ctxt) THEN
        Lexicographic_Order.lexicographic_order_tac false ctxt

    val thm = Goal.prove lthy frees [] prop (fn {context, ...} => tac context)
    val lthy' = Local_Theory.restore lthy
  in
    Morphism.thm (Proof_Context.export_morphism lthy lthy') thm
  end

(* based on Thy_Info.script_thy *)
fun script_thy pos txt thy =
  let
    val trs = flat
      [[Toplevel.init_theory (K thy) Toplevel.empty],
       Outer_Syntax.parse thy pos txt,
       [Toplevel.exit Toplevel.empty]]
    val end_state = fold (Toplevel.command_exception true) trs Toplevel.toplevel;
  in
    Toplevel.end_theory pos end_state
  end

fun try_timeout secs f x =
  let
    val time = Time.fromSeconds secs
  in
    Exn.capture (TimeLimit.timeLimit time f) x
  end

fun try_case_to_simps ctxt thm =
  the_default [thm] (try (Simps_Case_Conv.to_simps ctxt) thm)

fun restore_eq thm =
  case Thm.prop_of thm of
    @{term Trueprop} $ (Const (@{const_name HOL.eq}, _) $ _ $ _) => thm
  | _  => @{lemma "P \<Longrightarrow> P = True" by simp} OF [thm]

fun homogenize_spec_types ctxt thms =
  let
    val get_head = dest_Const o fst o strip_comb o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of
    val paired = map (`get_head) thms

    val head = map (fst o fst) paired
      |> distinct op =
      |> single_error "heads" @{here}

    val typ = Sign.the_const_type (Proof_Context.theory_of ctxt) head

    fun mk_subst (iname, (sort, inst)) =
      (Thm.ctyp_of ctxt (TVar (iname, sort)), Thm.ctyp_of ctxt inst)

    fun instantiate ((_, ttyp), thm) =
      let
        val subst = Type.raw_match (ttyp, typ) Vartab.empty |> Vartab.dest |> map mk_subst
      in
        Thm.instantiate (subst, []) thm
      end
  in
    map instantiate paired
  end

fun unify_all_types ctxt ts =
  let
    val unif = Pattern.unify_types (Context.Proof ctxt)
    fun aux (t1 :: t2 :: ts) env = aux (t2 :: ts) (unif (t1, t2) env)
      | aux _ env = env
  in
    aux ts
  end

fun homogenize_raw_types ctxt terms =
  let
    val terms = map Logic.varify_types_global terms

    val get_head = fst o dest_Free o fst o strip_comb o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop
    val heads = map get_head terms

    fun typ_occurences head =
      maps all_frees terms
      |> filter (equal head o fst)
      |> map snd

    val problem = map typ_occurences heads
    val env = Envir.empty (maxidx_of_typs (flat problem))

    val env' = fold (unify_all_types ctxt) problem env

    val solution = map_types (unvarify_typ o Envir.norm_type (Envir.type_env env'))
  in
    map solution terms
    |> Syntax.check_terms ctxt (* fail early if something's wrong *)
  end

fun if_to_cond_simps thm =
  case Thm.concl_of thm of
    @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ _ $ (Const (@{const_name If}, _) $ _ $ _ $ _)) =>
      maps (fn s => if_to_cond_simps (s OF [thm])) @{thms if_to_cond_simps}
  | _ =>
      [thm]