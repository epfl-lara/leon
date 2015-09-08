theory Leon_Ops
imports
  Protocol
  Codec_Class
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Simps_Case_Conv"
  Complex_Main
begin

named_theorems leon_unfold

ML_file "~~/src/HOL/TPTP/sledgehammer_tactics.ML"

sledgehammer_params [timeout = 5, provers = cvc4 z3 spass e]

lemma if_to_cond_simps:
  assumes "f = (if p then x else y)"
  shows "p \<Longrightarrow> f = x" "\<not> p \<Longrightarrow> f = y"
using assms by auto

ML_file "tactics.ML"
ML_file "util.ML"
ML_file "stateless_ops.ML"
ML_file "stateful_ops.ML"

operation_setup (auto) numeral_literal = \<open>Stateless_Ops.numeral\<close>
operation_setup (auto) word_literal = \<open>Stateless_Ops.word\<close>
operation_setup (auto) map_literal = \<open>Stateless_Ops.map\<close>
operation_setup (auto) serial_nat = \<open>Stateless_Ops.serial_nat\<close>
operation_setup (auto) load = \<open>Stateful_Ops.load\<close>
operation_setup (auto) "oracle" = \<open>Stateful_Ops.oracle\<close>
operation_setup (auto) fresh = \<open>Stateful_Ops.fresh\<close>
operation_setup (auto) prove = \<open>Stateful_Ops.prove\<close>
operation_setup (auto) equivalences = \<open>Stateful_Ops.equivalences\<close>
operation_setup (auto) assume_equivalences = \<open>Stateful_Ops.assume_equivalences\<close>
operation_setup (auto) "lemmas" = \<open>Stateful_Ops.lemmas\<close>
operation_setup (auto) assume_lemmas = \<open>Stateful_Ops.assume_lemmas\<close>
operation_setup (auto) "declare" = \<open>Stateful_Ops.declare\<close>
operation_setup (auto) pretty = \<open>Stateful_Ops.pretty\<close>
operation_setup (auto) report = \<open>Stateful_Ops.report\<close>
operation_setup (auto) dump = \<open>Stateful_Ops.dump\<close>
operation_setup (auto) lookup_datatype = \<open>Stateful_Ops.lookup_datatype\<close>
operation_setup (auto) "datatypes" = \<open>Stateful_Ops.datatypes\<close>
operation_setup (auto) "functions" = \<open>Stateful_Ops.functions\<close>
operation_setup (auto) cases = \<open>Stateful_Ops.cases\<close>

end