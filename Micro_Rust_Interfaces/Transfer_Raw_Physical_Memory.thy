(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Transfer_Raw_Physical_Memory
  imports Micro_Rust_Interfaces_Core.Raw_Physical_Memory
    Separation_Lenses.SLens
    Separation_Lenses.SLens_Pullback
begin

section\<open>Extending implementing of \<^locale>\<open>raw_tagged_physical_memory\<close> to larger separation algebras\<close>

text\<open>This theory uses the general pull back machinery to show that interpretations of the
\<^locale>\<open>raw_tagged_physical_memory\<close> locale can be extended along separation lenses.\<close>
locale raw_tagged_physical_memory_transfer =
   M: raw_tagged_physical_memory physical_memory_types_lo
  memset_phys_lo memset_phys_block_lo  points_to_tagged_phys_byte_lo store_physical_address_lo load_physical_address_lo
   tag_physical_page_lo + slens l
   for  l :: \<open>('s::sepalg, 't::sepalg) lens\<close> and
        physical_memory_types_lo :: \<open>'t \<Rightarrow> 'tag \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
        memset_phys_lo memset_phys_block_lo points_to_tagged_phys_byte_lo
        store_physical_address_lo load_physical_address_lo tag_physical_page_lo
begin

named_theorems lifted_defs
definition [lifted_defs]: \<open>memset_phys a b c \<equiv> l\<inverse> (memset_phys_lo a b c)\<close>
definition [lifted_defs]: \<open>memset_phys_block x y z \<equiv> l\<inverse> (memset_phys_block_lo x y z)\<close>
definition [lifted_defs]: \<open>points_to_tagged_phys_byte x y z t \<equiv> l\<inverse> (points_to_tagged_phys_byte_lo x y z t)\<close>
definition [lifted_defs]: \<open>store_physical_address x y \<equiv> l\<inverse> (store_physical_address_lo x y)\<close>
definition [lifted_defs]: \<open>load_physical_address x \<equiv> l\<inverse> (load_physical_address_lo x)\<close>
definition [lifted_defs]: \<open>tag_physical_page x y tag \<equiv> l\<inverse> (tag_physical_page_lo x y tag)\<close>

interpretation Defs: raw_tagged_physical_memory_defs \<open>\<lambda>(_::'s) (_::'tag) (_::'abort) (_ :: 'i prompt) (_::'o prompt_output). ()\<close>
  memset_phys memset_phys_block points_to_tagged_phys_byte
  store_physical_address load_physical_address tag_physical_page .

lemma raw_tagged_physical_memory_contracts_no_abort:
  shows \<open>\<And>a b c d. function_contract_abort (M.memset_tagged_phys_contract a b c d) = \<bottom>\<close>
    and \<open>\<And>a b c d. function_contract_abort (M.load_tagged_physical_address_contract a b c d) = \<bottom>\<close>
    and \<open>\<And>a b c d. function_contract_abort (M.store_tagged_physical_address_contract a b c d) = \<bottom>\<close>
  by (simp add: M.all_physical_memory_defs)+

text\<open>Since \<^verbatim>\<open>l\<inverse>\<close> commutes with all constructions carried out in the reference locale, all derived
definitions of functions and contracts are the pullbacks of their counterparts in the source type.\<close>
lemma raw_tagged_physical_memory_transfer_def_simps:
  shows \<open>\<And>a b c d. Defs.memset_tagged_phys_contract a b c d = l\<inverse> (M.memset_tagged_phys_contract a b c d)\<close>
    and \<open>\<And>a b c d. Defs.load_tagged_physical_address_contract a b c d = l\<inverse> (M.load_tagged_physical_address_contract a b c d)\<close>
    and \<open>\<And>a b c d. Defs.store_tagged_physical_address_contract a b c d = l\<inverse> (M.store_tagged_physical_address_contract a b c d)\<close>
  by (clarsimp simp add: slens_pull_back_simps simp add: lifted_defs pull_back_contract_def
    raw_tagged_physical_memory_defs.all_physical_memory_defs raw_tagged_physical_memory_contracts_no_abort bot_fun_def)+

lemma raw_tagged_physical_memory_lifted:
  shows \<open>raw_tagged_physical_memory memset_phys memset_phys_block
    points_to_tagged_phys_byte store_physical_address
    load_physical_address tag_physical_page\<close>
using M.all_raw_tagged_physical_memory_specs
  apply -
  apply (standard; (simp add: raw_tagged_physical_memory_transfer_def_simps)?)
  apply (clarsimp simp add: raw_tagged_physical_memory_contracts_no_abort pull_back_spec_universal
    lifted_defs intro!: slens_pull_back_intros simp flip: slens_pull_back_simps)+
  done

end

end