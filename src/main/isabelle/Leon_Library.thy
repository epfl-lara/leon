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

end