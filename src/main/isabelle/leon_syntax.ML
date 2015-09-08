signature LEON_SYNTAX = sig
  val setup: theory -> theory
end

structure Leon_Syntax: LEON_SYNTAX = struct

fun is_digit #"0" = true
  | is_digit #"1" = true
  | is_digit #"2" = true
  | is_digit #"3" = true
  | is_digit #"4" = true
  | is_digit #"5" = true
  | is_digit #"6" = true
  | is_digit #"7" = true
  | is_digit #"8" = true
  | is_digit #"9" = true
  | is_digit _ = false

fun is_leon_name base id name =
  let
    val prefix = Long_Name.append base (id ^ "'")
    val exploded = String.explode name
  in
    String.isPrefix prefix name andalso List.all is_digit (drop (String.size prefix) exploded)
  end

fun find_leon_name base id names =
  case filter (is_leon_name base id) names of
    [name] => SOME name
  | _ => NONE

fun translation const ctxt args =
  let
    val thy = Proof_Context.theory_of ctxt
    val thy_name = Context.theory_name thy
    val fixes = Variable.dest_fixes ctxt
    val {constants = consts, ...} =  Consts.dest (Sign.consts_of thy)
    fun guess id =
      if const then
        case find_leon_name thy_name id (map fst consts) of
          SOME name => Const (name, dummyT)
        | NONE => raise TERM ("unknown or ambiguous Leon constant " ^ id, args)
      else
        case find_leon_name "" id (map fst fixes) of
          SOME name => Free (name, dummyT)
        | NONE => raise TERM ("unknown or ambiguous Leon variable " ^ id, args)
  in
    case args of
      [(Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ _] => guess s
    | _ => impossible "Leon_Syntax.translation" @{here}
  end

val const_translation = translation true
val var_translation = translation false

val translation_setup = Sign.parse_translation
  [(@{syntax_const "_leon_var"}, var_translation),
   (@{syntax_const "_leon_const"}, const_translation)]


fun get_induct id thy =
  let
    val functions = Stateful_Ops.get_functions thy
    val names = Symtab.keys functions
  in
    case find_leon_name "" id names of
      SOME name =>
        (case the (Symtab.lookup functions name) of
          (NONE, _) => error ("no induction rule for " ^ id)
        | (SOME thm, _) => thm)
    | NONE => error ("unknown or ambiguous Leon function " ^ id)
  end

val attrib_setup =
  Attrib.setup @{binding leon_induct}
    (Scan.lift Args.name >>
      (fn name => Thm.mixed_attribute (fn (context, _) => (context, get_induct name (Context.theory_of context)))))
    "induction rule for Leon function"

val setup = translation_setup #> attrib_setup

end