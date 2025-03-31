(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Tuple
  imports Crush.Crush
begin
(*>*)

primrec zipWithNil :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b \<times> tnil) list" where
"zipWithNil xs [] = []" |
zipWithNil_Cons: "zipWithNil xs (y # ys) =
  (case xs of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, y, TNil) # zipWithNil zs ys)"

definition list_zip :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> ('s, ('a \<times> 'b \<times> tnil) list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>list_zip \<equiv> lift_fun2 zipWithNil\<close>

(*<*)
end
(*>*)