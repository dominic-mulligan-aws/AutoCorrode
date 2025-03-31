(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Common_Pitfalls
  imports 
    Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>Common pitfalls\<close>

subsection\<open>Code generation\<close>

subsubsection\<open>\<^verbatim>\<open>No code equations for ...\<close>\<close>

paragraph\<open>\<^verbatim>\<open>No code equations for prism_to_focus\<close>\<close>

text\<open>\<^verbatim>\<open>focus\<close> is defined as a subtype with invariant while \<^verbatim>\<open>prism\<close> encompasses all prisms,
including invalid ones (this is unavoidable since types must be inhabited, but there is no
valid prism between any two types -- in contrast, there \<^emph>\<open>is\<close> a focus between any two types).

The prism-to-focus conversion \<^verbatim>\<open>prism_to_focus\<close> is therefore only defined in the context of
\<^emph>\<open>valid\<close> prisms, and all theorems about it are constrained accordingly. In particular, the
theorem normally used for code equations is constrained:\<close>

thm prism_to_focus.rep_eq \<comment>\<open>\<^verbatim>\<open>is_valid_prism ?p \<Longrightarrow> Rep_focus (\<integral>\<^sub>p ?p) = \<integral>'\<^sub>p ?p\<close>\<close>

text\<open>Therefore, \<^verbatim>\<open>prism_to_focus\<close> cannot be code-extracted as-is. Instead, it has to be explicitly
instantiated with a valid prism. This then transfers to any function making use of \<^verbatim>\<open>prism_to_focus\<close>.

Here's a trivial example:\<close>

definition lift_to_focus_and_evaluate :: \<open>('a, 'b) prism \<Rightarrow> 'a \<Rightarrow> 'b option\<close>
  where \<open>lift_to_focus_and_evaluate p a \<equiv> focus_view (prism_to_focus p) a\<close>

text\<open>If you attempt to generate code from this, it won't work:\<close>

\<comment>\<open>export_code lift_to_focus_and_evaluate in OCaml (* No code equations for prism_to_focus *)\<close>

text\<open>Let's assume we know which prism(s) the function should be instantiated with:\<close>

definition prism_id :: \<open>(nat, nat) prism\<close> where \<open>prism_id \<equiv> iso_prism id id\<close>
lemma prism_id_valid: \<open>is_valid_prism prism_id\<close>
  by (simp add: iso_prism_valid prism_id_def)

definition \<open>lift_to_focus_and_evaluate_specialized a \<equiv> lift_to_focus_and_evaluate prism_id a\<close>

text\<open>Exporting this will still not work, unfortunately:\<close>

\<comment>\<open>
export_code lift_to_focus_and_evaluate_specialized in OCaml \<comment>\<open>No code equations for prism_to_focus\<close>
\<close>

text\<open>The reason is that the code-generator will still try to export \<^verbatim>\<open>lift_to_focus_and_evaluate\<close>
generically, while we need to enforce its inlining in the definition of \<^verbatim>\<open>lift_to_focus_and_evaluate_specialized\<close>.
Because this will be needed with \<^emph>\<open>every\<close> definition using \<^verbatim>\<open>lift_to_focus_and_evaluate\<close>, we mark
\<^verbatim>\<open>lift_to_focus_and_evaluate\<close> itself as always-inline using \<^verbatim>\<open>code_unfold\<close>:\<close>

declare lift_to_focus_and_evaluate_def[code_unfold]

text\<open>Let's try generating the code now. Unfortunately, we still get the same error!\<close>

\<comment>\<open>
export_code lift_to_focus_and_evaluate_specialized in OCaml \<comment>\<open>No code equations for prism_to_focus\<close>
\<close>

text\<open>The solution, here, is to wrap concrete instances of \<^verbatim>\<open>prism_to_focus\<close> into \<^verbatim>\<open>focus\<close> and give
them explicit code equations:\<close>

definition prism_id_focus :: \<open>(nat, nat) focus\<close> where \<open>prism_id_focus \<equiv> prism_to_focus prism_id\<close>

text\<open>Now we can explicitly instantiate the conditional code equation for \<^verbatim>\<open>prism_to_focus\<close> to
get an unconditional code equation for \<^verbatim>\<open>prism_id_focus\<close>:\<close>
thm prism_to_focus.rep_eq[OF prism_id_valid]
declare prism_to_focus.rep_eq[OF prism_id_valid, code]

text\<open>Finally, we need to tell the code-generator to replace \<^verbatim>\<open>prism_to_focus prism_id\<close> by
\<^verbatim>\<open>prism_id_focus\<close> wherever it occurs:\<close>

thm prism_id_focus_def[symmetric]
declare prism_id_focus_def[symmetric, code_unfold]

text\<open>With this, we can finally generate code for \<^verbatim>\<open>lift_to_focus_and_evaluate_specialized\<close>:\<close>

export_code lift_to_focus_and_evaluate_specialized in OCaml

text\<open>This all seems complicated, but the final boilerplate is pretty short, so let's recapitulate
it here:

\<^verbatim>\<open>definition prism_id_focus :: \<open>(nat, nat) focus\<close> where \<open>prism_id_focus \<equiv> prism_to_focus prism_id\<close>
declare prism_to_focus.rep_eq[OF prism_id_valid, code]
declare prism_id_focus_def[symmetric, code_unfold]\<close>
\<close>

text\<open>This is what you need for any prism, plus a one-off \<^verbatim>\<open>code_unfold\<close> for any definition using
\<^verbatim>\<open>prism_to_focus\<close>. The prime example in our code-base is \<^verbatim>\<open>reference_new\<close>, which is marked as
\<^verbatim>\<open>code_unfold\<close>.\<close>

text\<open>For a complete example, see e.g. \<^verbatim>\<open>ll_example_gv_prism_ll_node\<close> in \<^file>\<open>Linked_List_Executable_Heap.thy\<close>.\<close>

paragraph\<open>\<^verbatim>\<open>No code equations for prism_to_focus\<close> in the context of \<^verbatim>\<open>reference_new\<close>\<close>

text\<open>When you provide a wrapper around \<^verbatim>\<open>reference_fun\<close> instantiating it with a specific prism,
make sure to eta-expand the definition! Otherwise, the inlining \<^verbatim>\<open>reference_fun\<close> won't happen!\<close>

\<comment>\<open>Bad example:
\<comment>\<open>\<^verbatim>\<open>definition my_ref_new \<equiv> reference_fun my_prism\<close>\<close>\<close>

\<comment>\<open>Good example:
\<comment>\<open>\<^verbatim>\<open>definition my_ref_new v \<equiv> reference_fun my_prism v\<close>\<close>\<close>

end
