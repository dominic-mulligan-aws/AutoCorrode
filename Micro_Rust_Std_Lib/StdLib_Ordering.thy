(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Ordering
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

datatype ordering
  = Less
  | Equal
  | Greater
notation_nano_rust ordering.Less ("Ordering::Less")
notation_nano_rust ordering.Equal ("Ordering::Equal")
notation_nano_rust ordering.Greater ("Ordering::Greater")

definition cmp_pure :: \<open>'a::{order} \<Rightarrow> 'a \<Rightarrow> ordering\<close> where
  \<open>cmp_pure x y \<equiv>
     if x < y then
       Less
     else if x = y then
       Equal
     else Greater\<close>

definition cmp :: \<open>'a::{order} \<Rightarrow> 'a \<Rightarrow> ('s, ordering, 'abort, 'i, 'o) function_body\<close> where
  \<open>cmp \<equiv> lift_fun2 cmp_pure\<close>

(*<*)
end
(*>*)