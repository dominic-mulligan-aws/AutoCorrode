(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Word_Cast_Simplifier
  imports "HOL-Library.Word" 
    Word_Lib.More_Word ListAdditional
    "HOL-Eisbach.Eisbach"
begin
(*>*)

section\<open>Tailored word lemma solver\<close>

text\<open>We want to use @{thm More_Word.unat_ucast_up_simp}, which only works if we can solve the
   condition on length inequality. Add the required ones to a named theorem list\<close>
named_theorems bit_length_simps

text\<open>Seemingly random yet carefully curated list of simplification rules for word arithmetic\<close>
declare Type_Length.len_bit0 [bit_length_simps]
declare Type_Length.len_num1 [bit_length_simps]
declare Nat.One_nat_def [bit_length_simps]
declare Nat.mult_Suc_right [bit_length_simps]
declare Nat.mult_0_right [bit_length_simps]
declare Groups.monoid_add_class.add.right_neutral [bit_length_simps]
declare Num.mult_num_simps [bit_length_simps]
declare Num.linordered_nonzero_semiring_class.le_numeral_simps [bit_length_simps]
declare Num.le_num_simps [bit_length_simps]
declare Num.arith_simps [bit_length_simps]
declare Power.semiring_numeral_class.power_numeral [bit_length_simps]
declare Num.pow.simps [bit_length_simps]
declare Num.sqr.simps [bit_length_simps]
declare Word.unat_bintrunc [bit_length_simps]
declare Bit_Operations.semiring_bit_operations_class.take_bit_numeral_numeral [bit_length_simps]
declare Bit_Operations.take_bit_num_simps [bit_length_simps]
declare Num.pred_numeral_simps [bit_length_simps]
declare Option.option.case [bit_length_simps]
declare Word.ucast_bintr [bit_length_simps]
declare Int.ring_1_class.of_int_numeral [bit_length_simps]

named_theorems word_cast_simps
declare unat_arith_simps [word_cast_simps]
declare bit_length_simps [word_cast_simps]

text\<open>The next lemmas are the critical ones that \<^verbatim>\<open>unat_arith\<close> is terrible at\<close>

declare More_Word.unat_ucast_up_simp [word_cast_simps]
declare More_Word.unat_of_nat_eq [word_cast_simps]

text\<open>Combining @{thm unat_arith_simps} with the regular simpset seems to blow up. So we do three
steps:
\begin{itemize}
\item
Simplifying with the provided simpset,
\item
Then simplifying only with our simpset,
\item
Then again with the provided ones. We also clarify the goal if possible.
\end{itemize}\<close>
method word_cast_simp uses simps =
  (clarify?; ((simp add: simps)?); simp only: word_cast_simps; ((simp add: simps)?))

text\<open>If we want to solve the goal with this, we can additionally always unfold common constants.
We create a separate named theorem list for this, so these constants can be declared to be unfolded
at a later time.\<close>
named_theorems solve_word_cast_simps
method solve_word_cast uses simps =
  (solves \<open>word_cast_simp simps: simps solve_word_cast_simps\<close>)

(*<*)
end
(*>*)