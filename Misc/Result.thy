(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Result
  imports Main
begin

text\<open>We model the Rust \<^verbatim>\<open>Result<A, B>\<close> type using a corresponding datatype.\<close>
datatype ('a,'b) result = Ok 'a | Err 'b

definition result_is_err :: \<open>('a, 'b) result \<Rightarrow> bool\<close> where
   \<open>result_is_err r \<equiv> (case r of Ok _ \<Rightarrow> False | Err _ \<Rightarrow> True)\<close>
definition result_is_ok :: \<open>('a, 'b) result \<Rightarrow> bool\<close> where
   \<open>result_is_ok  r \<equiv> (case r of Ok _ \<Rightarrow> True | Err _ \<Rightarrow> False)\<close>

definition over_result :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'e) result \<Rightarrow> ('b, 'e) result\<close> where
  \<open>over_result f r \<equiv> case r of Err e \<Rightarrow> Err e | Ok x \<Rightarrow> Ok (f x)\<close>

definition over_err :: \<open>('e \<Rightarrow> 'f) \<Rightarrow> ('a, 'e) result \<Rightarrow> ('a, 'f) result\<close> where
  \<open>over_err f r \<equiv> case r of Err e \<Rightarrow> Err (f e) | Ok x \<Rightarrow> Ok x\<close>

end