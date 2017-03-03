theory Leon_Library
imports Leon_Ops
begin

axiomatization
  error :: "nat \<Rightarrow> 'a"

declare [[code abort: error]]

declare null_rec[simp]
declare List.null_def[simp]
declare List.bind_def[simp]
declare Let_def[leon_unfold]
declare Product_Type.split[leon_unfold]
declare comp_apply[simp del]
declare comp_def[simp]
declare member_rec[simp]

lemma [simp]: "list_ex P xs = (\<not> list_all (Not \<circ> P) xs)"
by (induct xs) auto

syntax "_leon_var" :: "idt \<Rightarrow> 'a" ("<var _>")
syntax "_leon_const" :: "idt \<Rightarrow> 'a" ("<const _>")

ML_file "leon_syntax.ML"

setup \<open>Leon_Syntax.setup\<close>

type_synonym int32 = "32 word"

definition select :: "'a list => int32 => 'a" where
[simp]: "select xs n = xs ! unat n"

definition update :: "'a list => int32 => 'a => 'a list" where
[simp]: "update xs n = list_update xs (unat n)"

definition length :: "'a list => int32" where
[simp]: "length xs = of_nat (List.length xs)"

definition replicate :: "int32 => 'a => 'a list" where
[simp]: "replicate n = List.replicate (unat n)"

end
