(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Bitfields
  imports
    WordAdditional Word_Lib.Bit_Shifts_Infix_Syntax
begin
(*>*)

section \<open>Utility functions for working with bitfields\<close>

(*<*)
context
begin

unbundle bit_operations_syntax
(*>*)

text\<open>Extract a subfield, or range of bits, from an input word given a position and length of the
subfield.  Implicitly casts the subfield out of the original input word's length into another.\<close>
definition extract_subfield :: \<open>'a::{len} word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b::{len} word\<close> where
  \<open>extract_subfield w position l \<equiv>
     ucast ((w >> position) AND ((1 << l) - 1))\<close>

text\<open>Write a subfield at a position in a given word.\<close>
definition write_subfield :: \<open>'a::{len} word \<Rightarrow> nat \<Rightarrow> 'b::{len} word \<Rightarrow> 'a::{len} word\<close> where
  \<open>write_subfield w position f \<equiv>
     let mask = (1 << LENGTH('b)) - 1 in
       (w AND NOT (mask << position)) OR ((ucast f AND mask) << position)\<close>

(*<*)
end

end
(*>*)
