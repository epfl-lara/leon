signature STATEFUL_OPS = sig
  val load: string * string * (string * string) list -> string list
  val oracle: unit -> unit
  val fresh: string -> string
  val prove: term list * string option -> string option
  val declare: string list -> unit
  val cases: (term * (string * typ) list) * (typ * (term * term) list) -> term
  val equivalences: (string * string) list -> string list
  val assume_equivalences: (string * string) list -> unit
  val lemmas: (string * term) list -> string list
  val assume_lemmas: (string * term) list -> unit
  val functions: (string * (string * typ) list * (term * typ)) list -> string option
  val datatypes: (string * string list * (string * (string * typ) list) list) list -> string option
  val lookup_datatype: string * (string * string) list -> (string, (string * (term * term * term list)) list) Codec.either
  val pretty: term -> string
  val report: unit -> (string * string) list
  val dump: unit -> (string * string) list

  (* internal *)
  val reset: theory option -> unit
  val peek: unit -> local_theory option
  val get_functions: theory -> (thm option * thm list) Symtab.table
end

structure Stateful_Ops: STATEFUL_OPS = struct

fun try_timeout' f = try_timeout 5 f (* global timeout for auxiliary operations *)

fun err_timeout msg f x =
  case try_timeout 5 f x of
    Exn.Res r => r
  | Exn.Exn TimeLimit.TimeOut => raise Timeout msg
  | Exn.Exn exn => reraise exn

datatype report =
  Function of {names: string list, raws: string list, specs: string list, inducts: (string * string) list} |
  Datatype of string |
  Theory of {import: string, scripts: (string * string) list} |
  Equivalence of string |
  Lemma of {name: string, prop: string} |
  Oracle

structure Reports = Theory_Data
(
  type T = report list
  val empty = []
  fun merge _ = impossible "Reports.merge" @{here}
  val extend = I
)

structure Functions = Theory_Data
(
  type T = (thm option * thm list) Symtab.table
  val empty = Symtab.empty
  fun merge _ = impossible "Functions.merge" @{here}
  val extend = I
)

structure Oracle = Theory_Data
(
  type T = (cterm -> thm) option
  val empty = NONE
  fun merge _ = impossible "Oracle.merge" @{here}
  val extend = I
)

fun add_report report = Reports.map (fn list => report :: list)
val add_fun = Functions.map o Symtab.update_new
val add_funs = fold add_fun
fun set_oracle thy =
  let
    val ((_, oracle), thy') = Thm.add_oracle (@{binding leon_oracle}, I) thy
  in
    Oracle.map (K (SOME oracle)) thy'
    |> add_report Oracle
  end
val get_oracle =
  Proof_Context.theory_of
  #> Oracle.get
  #> the_error "expected oracle" @{here}

val get_functions = Functions.get

type state = local_theory option
val empty_state = NONE: state

val state = Synchronized.var "libisabelle.leon_state" empty_state

fun unset_parallel_proofs () =
  Goal.parallel_proofs := 0

fun reset thy =
  (unset_parallel_proofs (); Synchronized.change state (K (Option.map (Named_Target.theory_init) thy)))

fun peek () =
  Synchronized.value state

local
  fun not_loaded pos =
    invalid_state "no theory loaded" pos
  fun already_loaded lthy =
    invalid_state ("theory " ^ Context.theory_name (Proof_Context.theory_of lthy) ^ "already loaded")
in

fun access_loaded f =
  case Synchronized.value state of
    SOME thy => f thy
  | NONE => not_loaded @{here}

fun update_loaded f =
  let
    fun upd NONE = not_loaded @{here}
      | upd (SOME thy) = let val (a, thy') = f thy in (a, SOME thy') end
  in
    Synchronized.change_result state upd
  end

fun load (root_name, thy_name, scripts) =
  let
    val _ = unset_parallel_proofs ()
    val _ =
      if Execution.is_running_exec Document_ID.none then ()
      else invalid_state "Must not be running in interactive mode" @{here}
    val root = Thy_Info.get_theory root_name

    fun load_script (name, txt) =
      let
        val thy = Theory.begin_theory (name, Position.none) [root]
      in (name, Exn.interruptible_capture (script_thy Position.none txt) thy) end

    fun classify (_, Exn.Res thy) = ([thy], [])
      | classify (name, Exn.Exn _) = ([], [name])

    fun upd (SOME lthy) = already_loaded lthy @{here}
      | upd NONE =
          let
            val (good, bad) = map classify (Par_List.map load_script scripts)
              |> split_list ||> flat |>> flat

            fun thy () =
              Theory.begin_theory (thy_name, Position.none) (root :: good)
              |> add_report (Theory {import = root_name, scripts = scripts})

            val res =
              if null bad then
                SOME (Named_Target.theory_init (thy ()))
              else
                NONE
          in (bad, res) end
  in Synchronized.change_result state upd end

end

fun oracle () =
  update_loaded (Local_Theory.background_theory set_oracle #> pair ())

fun fresh n =
  update_loaded (Variable.variant_fixes [n] #>> hd)

fun prove (ts, method) =
  access_loaded (fn lthy =>
    let
      val (ts', lthy) = register_terms ts lthy
      val prop = Balanced_Tree.make HOLogic.mk_disj ts'
      fun tac ctxt =
        case method of
          NONE => prove_tac ctxt
        | SOME src => HEADGOAL (method_tac @{here} src ctxt)
    in
      (* Assumption: all proofs are sequential *)
      try (Goal.prove lthy [] [] prop) (fn {context, ...} => tac context)
      |> Option.map (print_thm lthy)
    end)

fun gen_lemmas prove props =
  update_loaded (fn lthy =>
    let
      fun process (name, prop) lthy =
        let
          val ([prop'], lthy') = register_terms [prop] lthy
          val binding = Binding.qualified true "lemma" (Binding.make (name, @{here}))
        in
          case prove lthy' prop' of
            NONE => ([name], lthy)
          | SOME thm =>
              lthy (* sic *)
              |> Local_Theory.note ((binding, @{attributes [simp]}), [thm]) |> snd
              |> Local_Theory.background_theory (add_report (Lemma {name = name, prop = print_thm lthy thm}))
              |> pair []
        end
    in
      fold_map process props lthy
      |>> flat
    end)

val lemmas =
  gen_lemmas (fn ctxt => fn goal =>
    try_timeout' (Goal.prove ctxt [] [] goal) (fn {context, ...} => prove_tac context) |> Exn.get_res)

val assume_lemmas =
  gen_lemmas (fn ctxt => fn goal =>
    SOME (get_oracle ctxt (Thm.cterm_of ctxt goal)))
  #> K ()

fun declare names =
  update_loaded (fold Variable.declare_names (map (Free o rpair dummyT) names) #> pair ())

fun cases ((raw_scr, bounds), (expected_typ, clauses)) =
  access_loaded (fn ctxt =>
    let
      fun dest_abs (name, typ) t = Term.dest_abs (name, typ, t)
      val unbound = fold_map dest_abs bounds #> snd

      val scr = Syntax.check_term ctxt (unbound raw_scr)
      val scr_typ = fastype_of scr
      val names = Variable.names_of ctxt

      fun process_clause (raw_pat, raw_rhs) =
        let
          val pat = Syntax.check_term ctxt (Type.constraint scr_typ raw_pat)
          val frees = all_undeclared_frees ctxt pat
          val (free_names', ctxt') = Variable.add_fixes (map fst frees) ctxt
          val frees' = map Free (free_names' ~~ map snd frees)
          val frees = map Free frees
          val (pat', raw_rhs') = apply2 (subst_free (frees ~~ frees')) (pat, unbound raw_rhs)

          val rhs' =
            Type.constraint expected_typ raw_rhs'
            |> Syntax.check_term (Variable.declare_term pat' ctxt')
        in
          (pat', rhs')
        end

      val term =
         map process_clause clauses
         |> Case_Translation.make_case ctxt Case_Translation.Quiet names scr
         |> Syntax.check_term ctxt

      fun find_type (t $ u) name = merge_options (find_type t name, find_type u name)
        | find_type (Abs (_, _, t)) name = find_type t name
        | find_type (Free (name', typ)) name = if name = name' then SOME typ else NONE
        | find_type _ _ = NONE

      fun get_type (name, typ) =
        if typ = dummyT then
          the_default dummyT (find_type term name)
        else
          typ

      val new_bounds = map fst bounds ~~ map get_type bounds
    in
      fold (Term.lambda o Free) new_bounds term |> strip_abs_body
    end)

fun gen_equivalences prove eqs =
  update_loaded (fn lthy =>
    let
      fun prepare (lhs, rhs) =
        let
          val lhs' = qualify lthy lhs

          val (rule, specs) =
            Symtab.lookup (Functions.get (Proof_Context.theory_of lthy)) lhs
            |> the_error "equivalences" @{here}

          val goal = mk_untyped_eq (Const (lhs', dummyT), Syntax.parse_term lthy rhs)
            |> HOLogic.mk_Trueprop
            |> Syntax.check_term lthy
        in
          (lhs, specs, goal, rule)
        end

      val prepared = map prepare eqs

      fun process (name, specs, goal, rule) lthy =
        let
          val binding = Binding.qualified true "equiv" (Binding.make (name, @{here}))
        in
          case prove lthy goal rule of
            NONE => (([name], []), lthy)
          | SOME thm =>
              lthy
              |> Local_Theory.note ((Binding.empty, @{attributes [simp del]}), specs) |> snd
              |> Local_Theory.note ((binding, @{attributes [simp]}), [thm]) |> snd
              |> pair ([], [thm])
        end

      val ((bad, good), lthy') =
        fold_map process prepared lthy
        |>> split_list |>> apfst flat |>> apsnd flat

      val lthy'' =
        Local_Theory.background_theory (fold (add_report o Equivalence o print_thm lthy') good) lthy'
    in
      (bad, lthy'')
    end)

val assume_equivalences =
  gen_equivalences (fn lthy => fn goal => fn _ =>
    SOME (get_oracle lthy (Thm.cterm_of lthy goal)))
  #> K ()

val equivalences =
  gen_equivalences (fn lthy => fn goal => fn rule =>
    try_timeout' (Goal.prove lthy [] [] goal) (fn {context, ...} => equiv_tac rule context) |> Exn.get_res)

fun functions raw_funs =
  update_loaded (fn lthy =>
    let
      fun transform (name, raw_args, (raw_rhs, expected_typ)) =
        let
          val lhs = list_comb (Free (name, dummyT), map Free raw_args)
          val rhs = Type.constraint expected_typ raw_rhs
        in
          ((Binding.make (name, @{here}), NONE, NoSyn),
           HOLogic.mk_Trueprop (Const (@{const_name HOL.eq}, dummyT) $ lhs $ rhs))
        end

      val no_args = exists (equal 0 o length o #2) raw_funs

      val specs =
        map transform raw_funs
        |> split_list
        ||> map (Syntax.check_term lthy)
        ||> length raw_funs > 1 ? homogenize_raw_types lthy
        ||> map (pair (Binding.empty, []))
        |> op ~~

      val recursive =
        case specs of
          [(_, (_, prop))] =>
            let
              val ((f, _), rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop prop) |>> strip_comb
            in
              exists (equal f o Free) (all_frees rhs)
            end
        | _ => true

      fun fun_construction lthy =
        let
          val (heads, props) = split_list specs
          val construction = Function.add_function heads props Function_Fun.fun_config pat_completeness_auto_tac
          val (_, lthy) = err_timeout "function construction" construction lthy
          val (info, lthy) = err_timeout "termination proof" (Function.prove_termination NONE (termination_tac lthy)) lthy
        in
          #simps info
          |> the_error "simps of function definition" @{here}
          |> rpair lthy
        end
      fun def_construction lthy =
        let val [(head, prop)] = specs in
          Specification.definition (SOME head, prop) lthy
          |>> snd |>> snd |>> single
        end

      fun construction lthy = lthy |>
        (case (recursive, no_args) of
          (true, true) => raise Unsupported ("Mutual definition without arguments: " ^ commas (map #1 raw_funs))
        | (true, false) => fun_construction
        | (false, _) => def_construction)
    in
      case Exn.interruptible_capture construction lthy of
        Exn.Res (thms, lthy) =>
          let
            val names = map #1 raw_funs
            val lthy' = Local_Theory.restore lthy
            val thms = Proof_Context.export lthy lthy' thms
            val simpss = thms
              |> map (try_case_to_simps lthy' o restore_eq o full_simplify (mk_simp_ctxt lthy'))
              |> map (homogenize_spec_types lthy')
            val simps = maps if_to_cond_simps (flat simpss)
            val specs = names ~~ map (`(try_timeout' (mk_induction_schema lthy') #> Exn.get_res)) simpss
            fun print_induct (_, (NONE, _)) = NONE
              | print_induct (name, (SOME rule, _)) = SOME (name, print_thm lthy' rule)
            val binding = Binding.qualified true "spec" (Binding.make (hd names, @{here}))
            val report =
              Function
                {names = names,
                 inducts = map_filter print_induct specs,
                 specs = map (print_thm lthy') simps,
                 raws = map (print_thm lthy') thms}
            val lthy'' = lthy'
              |> Local_Theory.note ((Binding.empty, @{attributes [simp del]}), thms) |> snd
              |> Local_Theory.note ((binding, @{attributes [simp]}), simps) |> snd
              |> Local_Theory.background_theory (add_funs specs #> add_report report)
          in
            (NONE, lthy'')
          end
      | Exn.Exn (exn as Impossible _) =>
          reraise exn
      | Exn.Exn exn =>
          (SOME (print_exn exn), lthy)
    end)

fun datatypes raw_dts =
  update_loaded (fn lthy =>
    let
      val raw_dts = map (apfst (qualify lthy o #1) o dupl) raw_dts

      fun mk_edges (qname, (_, _, constrs)) =
        let
          fun collect_types (Type (name, typs)) = name :: maps collect_types typs
            | collect_types _ = []
          val deps = constrs |> maps snd |> maps (collect_types o snd)
        in map (pair qname) deps end

      fun free tp = TFree ("'" ^ tp, @{sort type})

      fun homogenize ((dt as (_, tps, _)) :: dts) =
        let
          fun subst tps' = typ_subst_atomic (map free tps' ~~ map free tps)
          fun replace (name, tps', constrs) = (name, tps, map (apsnd (map (apsnd (subst tps')))) constrs)
        in
          dt :: map replace dts
        end

      val sccs = compute_sccs raw_dts (maps mk_edges raw_dts)

      fun check_arity_dts dts = length (distinct op = (map (length o #2) dts)) = 1
      val check_arity = not (exists (equal false) (map check_arity_dts sccs))

      fun transform_tp raw_tp =
        (SOME (Binding.name raw_tp), (free raw_tp, @{sort type}))
      fun transform_field (name, typ) =
        (Binding.name ("s" ^ name), typ)
      fun transform_constr (name, raw_fields) =
        (((Binding.name ("d" ^ name), Binding.name ("c" ^ name)), map transform_field raw_fields), NoSyn)
      fun transform (name, raw_tps, raw_constrs) =
        let
          val dt = ((map transform_tp raw_tps, Binding.make (name, @{here})), NoSyn)
          val constrs = map transform_constr raw_constrs
        in
          (((dt, constrs), (@{binding map}, @{binding rel})), [])
        end

      fun print lthy dts =
        let
          fun print_tp tp = "'" ^ tp
          fun print_tps [] = ""
            | print_tps tps = enclose "(" ")" (commas (map print_tp tps))
          fun print_field (name, typ) =
            "(s" ^ name ^ ": " ^ quote (print_typ lthy typ) ^ ")"
          fun print_constr (name, fields) =
            "d" ^ name ^ ": c" ^ name ^ " " ^ space_implode " " (map print_field fields)
          fun print_one (name, tps, constrs) =
            print_tps tps ^ " " ^ name ^ " = " ^ space_implode " | " (map print_constr constrs)
        in
          "datatype " ^ space_implode " and " (map print_one dts)
        end

      fun setup_dts scc lthy =
        let
          val input = (Ctr_Sugar.default_ctr_options, map transform scc)
          val lthy =
            BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp input lthy
            |> Local_Theory.restore

          fun get_sugar (name, _, _) =
            qualify lthy name |> Ctr_Sugar.ctr_sugar_of lthy
            |> the_error ("ctr_sugar of " ^ name) @{here}

          val sugars = map get_sugar scc

          fun get_splits {split, split_asm, ...} = [split, split_asm]
          fun get_cases {case_thms, ...} = case_thms
        in
          lthy
          |> Local_Theory.note ((Binding.empty, @{attributes [split]}), maps get_splits sugars) |> snd
          |> Local_Theory.note ((Binding.empty, @{attributes [leon_unfold]}), maps get_cases sugars) |> snd
        end
    in
      if check_arity then
        let
          val sccs = map homogenize sccs
          val lthy' = fold setup_dts sccs lthy
          val lthy'' = Local_Theory.background_theory (fold (add_report o Datatype o print lthy') sccs) lthy'
        in (NONE, lthy'') end
      else
        (SOME "Unsupported feature: mismatched datatype arity", lthy)
    end)

fun lookup_datatype (name, raw_constructors) =
  update_loaded (fn lthy =>
    case Ctr_Sugar.ctr_sugar_of lthy name of
      NONE =>
        (Codec.Left ("unknown datatype " ^ name), lthy)
    | SOME {ctrs, discs, selss, split, split_asm, case_thms, ...} =>
        let
          val raw_constructors = sort_wrt snd (raw_constructors)
          val (names, terms) =
            map (fst o dest_Const) ctrs ~~ (discs ~~ selss)
            |> sort_wrt fst
            |> split_list
          fun process (internal_name, name) (disc, sels) =
            (internal_name, (Const (name, dummyT), dummify_types disc, map dummify_types sels))

          val lthy' =
            lthy
            |> Local_Theory.note ((Binding.empty, @{attributes [split]}), [split, split_asm]) |> snd
            |> Local_Theory.note ((Binding.empty, @{attributes [leon_unfold]}), case_thms) |> snd
        in
          if map snd raw_constructors <> names then
            (Codec.Left ("constructor name mismatch: declared constructors are " ^ commas names), lthy)
          else
            (Codec.Right (map2 process raw_constructors terms), lthy')
        end)

fun pretty t =
  access_loaded (fn lthy => print_term lthy t)

fun report () =
  access_loaded (fn lthy =>
    let
      fun print_report (Theory {scripts, ...}) = map (pair "Script" o fst) scripts
        | print_report (Equivalence prop) = [("Equivalence", prop)]
        | print_report (Datatype spec) = [("Datatype", spec)]
        | print_report (Lemma {name, prop}) = [("Lemma", name ^ ": " ^ prop)]
        | print_report (Function {raws, inducts, specs, ...}) =
            map (pair "Function (raw)") raws @
            map (pair "Function (spec)") specs @
            map (fn (name, induct) => ("Function (induct)", name ^ ": " ^ induct)) inducts
        | print_report Oracle = [("Oracle", "enabled")]
    in
      Proof_Context.theory_of lthy
      |> Reports.get
      |> rev
      |> maps print_report
    end)

fun dump () =
  access_loaded (fn lthy =>
    let
      fun print_thy_header name imports =
        "theory " ^ name ^ "\n" ^
        "imports " ^ space_implode " " imports ^ "\n" ^
        "begin\n"

      fun print_thy name import text =
        print_thy_header name [import] ^ text ^ "\nend\n"

      val name = Context.theory_name (Proof_Context.theory_of lthy)

      fun print_report (Theory {scripts, import}) =
            (map (fn (script_name, text) => (script_name, print_thy script_name import text)) scripts,
             print_thy_header name (import :: map fst scripts))
        | print_report (Equivalence prop) = ([], "lemma [simp]: " ^ quote prop ^ "\nsorry")
        | print_report (Lemma {prop, ...}) = ([], "lemma [simp]: " ^ quote prop ^ "\nsorry")
        | print_report (Datatype spec) = ([], spec)
        | print_report Oracle = ([], "")
        | print_report (Function {names, specs, ...}) =
            ([], "fun " ^ space_implode " and " names ^ " where\n" ^ space_implode "|\n" (map quote specs))
    in
      Proof_Context.theory_of lthy
      |> Reports.get
      |> rev
      |> map print_report
      |> split_list
      |>> flat
      ||> space_implode "\n\n"
      ||> pair name
      |> swap
      |> op ::
    end)

end