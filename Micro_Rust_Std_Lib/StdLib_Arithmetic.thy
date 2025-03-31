(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Arithmetic
  imports Crush.Crush StdLib_References
begin
(*>*)

subsection\<open>Arithmetic\<close>

definition overflowing_mul :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_mul x y \<equiv> FunctionBody(literal (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition overflowing_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_add x y \<equiv> FunctionBody (literal (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition wrapping_add_unsigned :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_add_unsigned \<equiv> \<lambda>self rhs. FunctionBody (literal (self + rhs))\<close>

definition word_sub_saturating_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
  \<open>word_sub_saturating_core e f \<equiv> if e < f then 0 else e - f\<close>

definition saturating_sub :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>saturating_sub e f \<equiv> FunctionBody (literal (word_sub_saturating_core e f))\<close>

definition checked_mul_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_mul_core w v \<equiv>
     if unat w * unat v \<ge> 2^LENGTH('a) then None else Some (w * v)\<close>

definition checked_add_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_add_core w v \<equiv>
     if unat w + unat v \<ge> 2^LENGTH('a) then None else Some (w + v)\<close>

definition checked_mul :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_mul w v \<equiv> FunctionBody (literal (checked_mul_core w v))\<close>

definition checked_add :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_add w v \<equiv> FunctionBody (literal (checked_add_core w v))\<close>

definition div_ceil_pure :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close> where
  \<open>div_ceil_pure x y \<equiv> (x + y - 1) div y\<close>

definition div_ceil :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('machine, 'a word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil x y \<equiv> FunctionBody (literal (div_ceil_pure x y))\<close>

\<comment> \<open>Contracts and verifications\<close>

definition overflowing_mul_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close> where
  [crush_contracts]: \<open>overflowing_mul_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in \<comment> \<open>Any inputs are acceptable\<close>
    let post = \<lambda>ret. \<langle>ret = (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in \<comment> \<open>The specification is not different from the function body\<close>
      make_function_contract pre post\<close>
ucincl_auto overflowing_mul_contract

lemma overflowing_mul_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_mul x y \<Turnstile>\<^sub>F overflowing_mul_contract x y\<close>
by (crush_boot f: overflowing_mul_def contract: overflowing_mul_contract_def) crush_base

definition overflowing_add_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close>where
  [crush_contracts]: \<open>overflowing_add_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto overflowing_add_contract

lemma overflowing_add_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_add x y \<Turnstile>\<^sub>F overflowing_add_contract x y\<close>
by (crush_boot f: overflowing_add_def contract: overflowing_add_contract_def) crush_base

definition wrapping_add_unsigned_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_add_unsigned_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = x + y\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto wrapping_add_unsigned_contract

lemma wrapping_add_unsigned_spec [crush_specs]:
  shows \<open>\<Gamma> ; wrapping_add_unsigned x y \<Turnstile>\<^sub>F wrapping_add_unsigned_contract x y\<close>
by (crush_boot f: wrapping_add_unsigned_def contract: wrapping_add_unsigned_contract_def) crush_base

definition saturating_sub_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>saturating_sub_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = (if x < y then 0 else x - y)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto saturating_sub_contract

lemma saturating_sub_spec [crush_specs]:
  shows \<open>\<Gamma> ; saturating_sub x y \<Turnstile>\<^sub>F saturating_sub_contract x y\<close>
by (crush_boot f: saturating_sub_def contract: saturating_sub_contract_def)
  (crush_base simp add: word_sub_saturating_core_def)

definition div_ceil_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>div_ceil_contract x y \<equiv>
    let pre  = \<top>;
        post = \<lambda>ret. \<langle>ret = (x + y - 1) div y\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto div_ceil_contract

lemma div_ceil_spec [crush_specs]:
  shows \<open>\<Gamma> ; div_ceil x y \<Turnstile>\<^sub>F div_ceil_contract x y\<close>
by (crush_boot f: div_ceil_def contract: div_ceil_contract_def) (crush_base simp add: div_ceil_pure_def)

(*<*)
end
(*>*)