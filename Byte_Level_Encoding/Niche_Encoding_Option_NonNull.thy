(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Niche_Encoding_Option_NonNull
  imports Byte_Encoding_Word_Nat
begin
(*>*)

section\<open>Niche encoding for optional non-null pointers\<close>

text\<open>This section defines the niche encoding for \<^verbatim>\<open>Option<NonNull>\<close>.\<close>

subsection\<open>The \<^verbatim>\<open>NonNull\<close> type\<close>

text\<open>The following is the type of non-null raw pointers\<close>

typedef NonNullRaw = \<open>{a :: 64 word. a \<noteq> 0}\<close>
  using one_neq_zero by blast

(*<*)
setup_lifting type_definition_NonNullRaw
(*>*)

subsection\<open>Niche encoding: Abstractly\<close>

text\<open>On an abstract level, the niche encoding exploits that \<^verbatim>\<open>NonNullRaw option\<close> is isomorphic t
\<^verbatim>\<open>64 word\<close> by embedding \<^verbatim>\<open>None\<close> as \<^verbatim>\<open>0\<close>:\<close>

lift_definition as_raw_ptr :: \<open>NonNullRaw \<Rightarrow> 64 word\<close> is \<open>\<lambda>(x:: 64 word). x\<close> .

definition option_non_null_raw_to_raw_ptr :: \<open>NonNullRaw option \<Rightarrow> 64 word\<close> where
  \<open>option_non_null_raw_to_raw_ptr nn_opt \<equiv>
     case nn_opt of 
       None    \<Rightarrow> 0
     | Some nn \<Rightarrow> as_raw_ptr nn\<close>

lift_definition (code_dt) raw_ptr_to_option_non_null_raw :: \<open>64 word \<Rightarrow> NonNullRaw option\<close> is
  \<open>\<lambda>(ptr :: 64 word). 
     if ptr = 0 then
        None
     else
        Some ptr\<close> 
by auto

lemma raw_ptr_to_option_non_null_raw_cases:
  shows \<open>raw_ptr_to_option_non_null_raw 0 = None\<close>
    and \<open>ptr \<noteq> 0 \<Longrightarrow> map_option as_raw_ptr (raw_ptr_to_option_non_null_raw ptr) = Some ptr\<close>
proof -
  show \<open>raw_ptr_to_option_non_null_raw (0 :: 64 word) = None\<close>
    by (metis not_Some_eq option.map(2) raw_ptr_to_option_non_null_raw.rep_eq)
next 
  show \<open>ptr \<noteq> 0 \<Longrightarrow> map_option as_raw_ptr (raw_ptr_to_option_non_null_raw ptr) = Some ptr\<close>
    using as_raw_ptr.rep_eq raw_ptr_to_option_non_null_raw.rep_eq by presburger
qed

lemma option_non_null_raw_to_raw_ptr_inv:
  shows \<open>\<And>x. option_non_null_raw_to_raw_ptr (raw_ptr_to_option_non_null_raw x) = x\<close>
    and \<open>\<And>x. raw_ptr_to_option_non_null_raw (option_non_null_raw_to_raw_ptr x) = x\<close>
proof -
   fix x :: \<open>64 word\<close>
  show \<open>option_non_null_raw_to_raw_ptr (raw_ptr_to_option_non_null_raw x) = x\<close>
    by (simp add: Abs_NonNullRaw_inverse as_raw_ptr.rep_eq option_non_null_raw_to_raw_ptr_def
        raw_ptr_to_option_non_null_raw.abs_eq)
next
   fix x :: \<open>NonNullRaw option\<close>
  have \<open>\<And>n. Abs_NonNullRaw (as_raw_ptr n) = n\<close>
    using Rep_NonNullRaw_inverse as_raw_ptr.rep_eq by force
  moreover have \<open>\<And>n. as_raw_ptr n \<noteq> 0\<close>
    using Rep_NonNullRaw as_raw_ptr.rep_eq by auto
  ultimately show \<open>raw_ptr_to_option_non_null_raw (option_non_null_raw_to_raw_ptr x) = x\<close>
    by (simp add: option.case_eq_if option_non_null_raw_to_raw_ptr_def raw_ptr_to_option_non_null_raw.abs_eq)
qed

definition niche_encoding_abstract_iso_prism :: \<open>(64 word, NonNullRaw option) prism\<close> where
  \<open>niche_encoding_abstract_iso_prism \<equiv>
    iso_prism raw_ptr_to_option_non_null_raw option_non_null_raw_to_raw_ptr\<close>

lemma niche_encoding_abstract_iso_prism_valid:
  shows \<open>is_valid_prism niche_encoding_abstract_iso_prism\<close>
by (simp add: iso_prism_valid niche_encoding_abstract_iso_prism_def option_non_null_raw_to_raw_ptr_inv)

subsection\<open>Niche encoding: Concretely\<close>

text\<open>The 'concrete' Niche encoding combines the abstract Niche encoding isomorphism between
\<^verbatim>\<open>NonNullRaw option\<close> and \<^verbatim>\<open>64 word\<close> with the (little or big endian) byte encoding for
\<^verbatim>\<open>64 word\<close>.\<close>

definition niche_encoding_array_prism_be :: \<open>((byte, 8) array, NonNullRaw option) prism\<close> where
  \<open>niche_encoding_array_prism_be \<equiv>
    prism_compose word64_byte_array_iso_prism_be niche_encoding_abstract_iso_prism\<close>

definition niche_encoding_array_prism_le :: \<open>((byte, 8) array, NonNullRaw option) prism\<close> where
  \<open>niche_encoding_array_prism_le \<equiv>  
    prism_compose word64_byte_array_iso_prism_le niche_encoding_abstract_iso_prism\<close>

definition niche_encoding_list_prism_be :: \<open>(byte list, NonNullRaw option) prism\<close> where
  \<open>niche_encoding_list_prism_be \<equiv>  
    prism_compose list_fixlen_prism niche_encoding_array_prism_be\<close>

definition niche_encoding_list_prism_le :: \<open>(byte list, NonNullRaw option) prism\<close> where
  \<open>niche_encoding_list_prism_le \<equiv>  
    prism_compose list_fixlen_prism niche_encoding_array_prism_le\<close>

lemma niche_encoding_array_prism_validity: 
  shows \<open>is_valid_prism niche_encoding_array_prism_be\<close>
    and \<open>is_valid_prism niche_encoding_array_prism_le\<close>
    and \<open>is_valid_prism niche_encoding_list_prism_be\<close>
    and \<open>is_valid_prism niche_encoding_list_prism_le\<close>
by (auto intro!: prism_compose_valid simp add: niche_encoding_array_prism_be_def 
  niche_encoding_array_prism_le_def niche_encoding_list_prism_be_def niche_encoding_list_prism_le_def
  list_fixlen_prism_valid word_byte_array_iso_prism_validity niche_encoding_abstract_iso_prism_valid)

(*<*)
end
(*>*)