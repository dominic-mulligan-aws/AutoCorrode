(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Exception    
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

datatype 'a hal_abort = ExceptionReturn 'a

definition eret :: \<open>'a \<Rightarrow> ('s, 'v, 'a hal_abort, 'i, 'o) function_body\<close> where
  \<open>eret x \<equiv> FunctionBody (abort (CustomAbort (ExceptionReturn x)))\<close>

definition eret_contract :: \<open>'eret \<Rightarrow> ('s::{sepalg}, 'a, 'eret hal_abort) function_contract\<close> where
  [crush_contracts]: \<open>eret_contract e \<equiv>
    make_function_contract_with_abort UNIV \<bottom> (\<lambda>a. \<langle>a = CustomAbort (ExceptionReturn e)\<rangle>)\<close>
ucincl_auto eret_contract

lemma eret_spec [crush_specs]:
  shows \<open>\<Gamma>; eret e \<Turnstile>\<^sub>F eret_contract e\<close>
  by (crush_boot f: eret_def contract: eret_contract_def) crush_base

end
(*>*)