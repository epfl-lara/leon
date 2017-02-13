theory Leon_Types
imports
  "~~/src/HOL/Word/Word"
begin

typedecl string

datatype (discs_sels) 'a leon_dummy = Dummy
datatype (discs_sels) 'a lazy = Lazy "'a \<Rightarrow> unit"
datatype (discs_sels) 'a with_state = With_State 'a
datatype (discs_sels) 'a "fun" = Fun 'a
datatype (discs_sels) 'a star = Star 'a
datatype (discs_sels) 'a mem_with_state = Mem_With_State 'a
datatype (discs_sels) 'a task = Task 'a
datatype (discs_sels) ('s, 'a) state = State "'s \<Rightarrow> ('a \<times> 's)"
datatype (discs_sels) ('a, 'b) with_rel = With_Rel "'a" "'a \<Rightarrow> 'b \<Rightarrow> bool" bool
datatype (discs_sels) ('a, 'b) with_proof = With_Proof "'a" "'a \<Rightarrow> 'b \<Rightarrow> bool" bool bool
datatype (discs_sels) 'a ensuring = Ensuring 'a
datatype (discs_sels) proof_ops = Proof_Ops bool
datatype (discs_sels) boolean_decorations = Boolean_Decorations bool
datatype (discs_sels) 'a specs_decorations = Specs_Decorations 'a
datatype (discs_sels) string_decorations = String_Decorations string
datatype (discs_sels) 'a rel_reasoning = Rel_Reasoning 'a bool
datatype (discs_sels) rational = Rational int int

datatype (discs_sels) web_tree =
  Web_Attribute string string |
  Element string "web_tree list" "web_tree list" "web_tree list" |
  Web_Element_With_ID "web_tree" "32 word" |
  Text_Element string |
  Web_Style string string
datatype (discs_sels) style_rule = Style_Rule string "web_tree list"
datatype (discs_sels) style_sheet = Style_Sheet "style_rule list"
datatype (discs_sels) web_page = Web_Page web_tree style_sheet
datatype (discs_sels) web_site = Web_Site "web_page list"
datatype (discs_sels) web_page_ided = Web_Page_IDed web_tree style_sheet
datatype (discs_sels) web_site_ided = Web_Site_IDed "web_page_ided list"
datatype (discs_sels) 't acceptor = Acceptor string
datatype (discs_sels) 't css_acceptor = CSS_Acceptor string
datatype (discs_sels) element_decision = Element_Decision bool
datatype (discs_sels) style_builder = Style_Builder string

end