(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Range_Type
  imports Core_Expression Rust_Iterator
begin
(*>*)

section\<open>The \<^emph>\<open>Range\<close> type\<close>

datatype 'a range
  = Range   \<open>'a\<close> \<open>'a\<close> \<comment> \<open>Beginning, end of range, exclusive\<close>
  | RangeEq \<open>'a\<close> \<open>'a\<close> \<comment> \<open>Beginning, end or range, inclusive\<close>

text\<open>The range \<^term>\<open>Range start end\<close> contains all values with \<^term>\<open>start \<le> x \<and> x < end\<close>.
It is empty if \<^term>\<open>start \<ge> end\<close>. The range \<^term>\<open>RangeEq start end\<close> contains all
values with \<^term>\<open>start \<le> x \<and> x \<le> end\<close> and is empty if \<^term>\<open>start > end\<close>.\<close>

subsection\<open>Syntax for the \<^emph>\<open>Range\<close> type\<close>

subsection\<open>Core material related to the \<^emph>\<open>Range\<close> type\<close>

definition is_empty :: \<open>'a::{ord} range \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close>  where
  \<open>is_empty r \<equiv> FunctionBody
    (case r of
       Range s e   \<Rightarrow> literal (s \<ge> e)
     | RangeEq s e \<Rightarrow> literal (s > e))\<close>

definition contains :: \<open>'a::ord range \<Rightarrow> 'a \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>contains r x \<equiv> FunctionBody
    (case r of
       Range s e   \<Rightarrow> literal (s \<le> x \<and> x < e)
     | RangeEq s e \<Rightarrow> literal (s \<le> x \<and> x \<le> e))\<close>

definition range_new :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('s, 'a range, 'abort, 'i, 'o) function_body\<close> where
  \<open>range_new \<equiv> lift_fun2 Range\<close>

definition range_eq_new :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('s, 'a range, 'abort, 'i, 'o) function_body\<close> where
  \<open>range_eq_new \<equiv> lift_fun2 RangeEq\<close>

text\<open>Iterator for a range\<close>

fun range_into_list :: \<open>'a::len word range \<Rightarrow> 'a word list\<close> where
   \<open>range_into_list (Range s e) = List.map of_nat [unat s..<(unat e)]\<close> 
 | \<open>range_into_list (RangeEq s e) = List.map of_nat [unat s..<(unat e+1)]\<close>

definition make_iterator_from_range :: \<open>'b::{len} word range \<Rightarrow> ('a, 'b word, 'abort, 'i, 'o) iterator\<close> where
  [micro_rust_simps]: \<open>make_iterator_from_range r \<equiv> make_iterator_from_list (range_into_list r)\<close>

definition range_into_iter :: \<open>'a::{len} word range \<Rightarrow> ('s, ('s, 'a word, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  [micro_rust_simps]: \<open>range_into_iter r \<equiv> fun_literal (make_iterator_from_range r)\<close>

adhoc_overloading into_iter \<rightleftharpoons> range_into_iter

subsection\<open>Slice-like behavior from lists\<close>

definition len :: \<open>'a list \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>len xs \<equiv> FunctionBody (literal (of_nat (length xs)))\<close>

definition list_index :: \<open>'a list \<Rightarrow> 'w::len word \<Rightarrow> ('s,'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>list_index xs idx \<equiv> FunctionBody (
     case nth_opt (unat idx) xs of
       None \<Rightarrow> abort DanglingPointer
     | Some x \<Rightarrow> literal x)\<close>

definition array_index :: \<open>('a, 'l::{len}) array \<Rightarrow> 'w::len word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>array_index xs idx \<equiv> FunctionBody (
     if unat idx < array_len xs then
       literal (array_nth xs (unat idx))
     else
       abort DanglingPointer)\<close>
 
definition vector_index :: \<open>('a, 'l::{len}) vector \<Rightarrow> 'w::len word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>vector_index xs idx \<equiv> FunctionBody (
     if unat idx < vector_len xs then
       literal (vector_nth xs (unat idx))
     else
       abort DanglingPointer)\<close>

definition list_index_range :: \<open>'a list \<Rightarrow> 'w::len word range \<Rightarrow> ('s,'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>list_index_range xs rng \<equiv> FunctionBody (
    case rng of
      Range s e \<Rightarrow>
        if s \<ge> e then
          literal []
        else
          if unat e \<le> length xs then
            literal (take (unat (e-s)) (drop (unat s) xs))
          else
            abort DanglingPointer
    | RangeEq s e \<Rightarrow>
        if s > e then
          literal []
        else
          if unat e < length xs then
            literal (take (1 + unat (e-s)) (drop (unat s) xs))
          else
            abort DanglingPointer)\<close>

definition array_index_range :: \<open>('a, 'l::{len}) array \<Rightarrow> 'w::{len} word range \<Rightarrow>
      ('s, 'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>array_index_range arr rng \<equiv> list_index_range (array_to_list arr) rng\<close>

definition vector_index_range :: \<open>('a, 'l::{len}) vector \<Rightarrow> 'w::{len} word range \<Rightarrow>
      ('s, 'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>vector_index_range arr rng \<equiv> list_index_range (vector_to_list arr) rng\<close>

(*<*)
end
(*>*)
