(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust
  imports
    Bool_Type Bool_Type_Lemmas Core_Expression Core_Expression_Lemmas Core_Syntax Result_Type 
    Option_Type Range_Type Rust_Iterator Rust_Iterator_Lemmas Numeric_Types
    Numeric_Types_Lemmas Global_Store SSA Micro_Rust_Shallow_Embedding
begin
(*>*)

section\<open>Entry point for Micro Rust\<close>

text\<open>This theory's main purpose is to import all of the material related to Core Micro Rust.  It
also serves as a point where common material (for example, automation routines) can be placed.\<close>

subsection\<open>Symbolic execution of Core Micro Rust programs\<close>

text\<open>The following tactic transforms a Micro Rust expression appearing on the left-hand side of an
equality into an SSA normal form:\<close>

text\<open>The following tactic is able to close equations between semantically-equal Micro Rust programs
by symbolically executing them with our semantic equivalences:\<close>
method micro_rust_symbolic_execute =
  (rule expression_eqI; elim micro_rust_elims; clarsimp simp add: micro_rust_simps;
    intro micro_rust_intros; clarsimp simp add: micro_rust_simps)

term \<open>(match (return r) \<lbrace>
         \<guillemotleft>None\<guillemotright> \<Rightarrow> skip,
         \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> skip
       \<rbrace> ) = skip\<close>

text\<open>Some tests of the two tactics:\<close>
notepad
begin
  fix e :: \<open>String.literal\<close>
  have \<open>(match (panic e) \<lbrace>
          \<guillemotleft>None\<guillemotright> \<Rightarrow> skip,
          \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> s
        \<rbrace>) = panic e\<close>
    by micro_rust_symbolic_execute
next
  fix r :: \<open>('s, 'r, 'r, 'abort, 'i, 'o) expression\<close> and e :: \<open>String.literal\<close>
  have \<open>\<lbrace> match (return r) \<lbrace>
          \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
            if (panic e) \<lbrace>
              skip
            \<rbrace>
          \<rbrace>,
          \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> s
        \<rbrace> \<rbrace> =
        \<lbrace> let r = r;
          let x = return (\<up>r);
          match (\<up>x) \<lbrace>
            \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
              let y = panic e;
              if \<up>y \<lbrace> 
                skip
              \<rbrace>
            \<rbrace>,
            \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> s \<rbrace> \<rbrace>\<close>
    by micro_rust_ssa_normalize (simp add: bind_literal_unit)
next
  fix s e :: \<open>('s, 'a::{ord}, 'r, 'abort, 'i, 'o) expression\<close> and oof :: \<open>String.literal\<close>
  have \<open>(\<langle>s\<dots>e\<rangle>)\<cdot>contains\<langle>panic oof\<rangle> =
         (let s = s;
          let e = e;
          let r = \<langle>\<up>s\<dots>\<up>e\<rangle>;
          let x = panic oof;
            (\<up>r)\<cdot>contains\<langle>\<up>x\<rangle>)\<close>
    by micro_rust_ssa_normalize
end

(*<*)
end
(*>*)
