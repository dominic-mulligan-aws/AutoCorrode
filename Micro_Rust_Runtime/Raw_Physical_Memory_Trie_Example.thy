(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Physical_Memory_Trie_Example
  imports Raw_Physical_Memory_Trie
    Raw_Physical_Memory_Trie_PP
begin

section\<open>Manipulating physical memory directly\<close>

text\<open>In this section, we exemplify some of the top-level functions operating on physical
memory: Load/store of individual bytes, as well as bulk memset.\<close>

text\<open>Since the toplevel operations on \<^verbatim>\<open>tagged_physical_memory\<close> are uRust \<^verbatim>\<open>expression\<close>s, not
pure functions, we first need an evaluator for uRust. Here, we take the trivial evaluator which
does not expect any non-logging yields.\<close>
definition eval :: \<open>('s, 'a, unit, unit prompt, unit prompt_output) function_body
  \<Rightarrow> 's \<Rightarrow> 'a \<times> 's\<close> where
  \<open>eval f \<sigma> \<equiv>
    let cont = (deep_evaluate_det yield_handler_det_no_yield (call f) \<sigma>)
       :: ('s, 'a, 'a, unit, unit prompt, unit prompt_output) continuation
    in
    case cont of
      continuation.Success v \<sigma>' \<Rightarrow> (v, \<sigma>')
    | _ \<Rightarrow> undefined
  \<close>

text\<open>Now we can invoke the uRust functions operating on \<^verbatim>\<open>tagged_physical_memory\<close> as if they were
pure functions.

Let's start with a 0-ed memory\<close>
definition \<sigma>\<^sub>0 where \<open>\<sigma>\<^sub>0 \<equiv> physical_memory_tag_all_bytes 0 \<top> ()\<close>
value\<open>\<sigma>\<^sub>0\<close> (* "MEMORY \<lparr>\<lbrakk>0x0-0x1000000000000\<rbrakk>: 0\<rparr>" *)

text\<open>Let's set a single byte:\<close>
definition \<open>\<sigma>\<^sub>1 \<equiv> snd (eval (store_tagged_physical_address 0x0000000FF1CE 0x12) \<sigma>\<^sub>0)\<close>
value \<open>\<sigma>\<^sub>1\<close> (* "MEMORY \<lparr>\<lbrakk>0x0-0xFF1C0\<rbrakk>: 0, \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x12, 0], \<lbrakk>0xFF1D0-0x1000000000000\<rbrakk>: 0\<rparr>" *)

text\<open>Let's set a single byte:\<close>
definition \<open>\<sigma>\<^sub>2 \<equiv> snd (eval (store_tagged_physical_address 0x0000000FF1CF 0x13) \<sigma>\<^sub>1)\<close>
value \<open>\<sigma>\<^sub>2\<close>

text\<open>Let's memset a block range\<close>
definition \<open>\<sigma>\<^sub>3 \<equiv> snd (eval (memset_tagged_phys_block 0xDEADBEEF000 12 0x42) \<sigma>\<^sub>2)\<close>
value\<open>\<sigma>\<^sub>3\<close>
(* "MEMORY \<lparr>
   \<lbrakk>0x0-0xFF1C0\<rbrakk>: 0,
   \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x12, 0],
   \<lbrakk>0xFF1D0-0xDEADBEEF000\<rbrakk>: 0,
   \<lbrakk>0xDEADBEEF000-0xDEADBEF0000\<rbrakk>: 0x42,
   \<lbrakk>0xDEADBEF0000-0x1000000000000\<rbrakk>: 0\<rparr>" *)

\<comment>\<open>Next, let's memset an unaligned range overlapping with the previous block range:\<close>
definition \<open>\<sigma>\<^sub>4 \<equiv> snd( eval (memset_tagged_phys 0xDEADBEEF09A 0x12345 0x12) \<sigma>\<^sub>3)\<close>
value \<open>\<sigma>\<^sub>4\<close>
(* "MEMORY \<lparr>
  \<lbrakk>0x0-0xFF1C0\<rbrakk>: 0,
  \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x12, 0],
  \<lbrakk>0xFF1D0-0xDEADBEEF000\<rbrakk>: 0,
  \<lbrakk>0xDEADBEEF000-0xDEADBEEF090\<rbrakk>: 0x42,
  \<lbrakk>0xDEADBEEF090-0xDEADBEEF0A0\<rbrakk>: [0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12],
  \<lbrakk>0xDEADBEEF0A0-0xDEADBF013D0\<rbrakk>: 0x12,
  \<lbrakk>0xDEADBF013D0-0xDEADBF013E0\<rbrakk>: [0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0],
  \<lbrakk>0xDEADBF013E0-0x1000000000000\<rbrakk>: 0\<rparr>" *)

\<comment>\<open>Let's do some reads:\<close>
value \<open>fst (eval (load_tagged_physical_address 0x0000000FF1CD) \<sigma>\<^sub>4)\<close> (* "0x0" *)
value \<open>fst (eval (load_tagged_physical_address 0x0000000FF1CE) \<sigma>\<^sub>4)\<close> (* "0x12" *)
value \<open>fst (eval (load_tagged_physical_address 0xDEADBEEF09A) \<sigma>\<^sub>4)\<close> (* "0x12" *)
value \<open>fst (eval (load_tagged_physical_address 0xDEADBEEF099) \<sigma>\<^sub>4)\<close> (* "0x42" *)

end