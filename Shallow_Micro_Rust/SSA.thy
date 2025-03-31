(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory SSA
  imports Core_Expression_Lemmas Bool_Type_Lemmas Rust_Iterator_Lemmas
          "HOL-Library.Rewrite"
begin
(*>*)


subsection\<open>Converting expressions to SSA form\<close>

text\<open>This section shows that each expression of Core Micro Rust can be transformed into a form of
\<^emph>\<open>single static assignment\<close> (or SSA, henceforth) wherein every effectful computation (i.e., an
expression which may return early, for example) is localized within the binding of a \<^verbatim>\<open>let\<close>
expression.  As a result of this, when defining Hoare-style triples later, and when also defining
rules for the Weakest Precondition calculus, we only need to consider terms in this SSA form.  This
massively simplifies some of the rules as we need not consider an early return from the discriminant
expression in a conditional, for example.

Note below that we use a ``trick'' to ensure that simplification using these rules remains tightly
controlled.  Namely, we use the \<^verbatim>\<open>MICRO_RUST_SSA_CONTROL\<close> function, which is merely the identity
function, to ``mark'' exactly where we want SSAification to apply: compound expressions are
simplified from the ``outside in'' wherein we push the \<^verbatim>\<open>MICRO_RUST_SSA_CONTROL\<close> inwards towards
new terms that must be simplified.  In this way, we stop simplification looping forever, constantly
trying to hoist the discriminant term out of a conditional or match expression, for example.  In
effect, we use simplification but bake a \<^emph>\<open>rewrite strategy\<close> of our own design into the
simplification engine using this trick.\<close>

definition MICRO_RUST_SSA_CONTROL :: \<open>'a \<Rightarrow> 'a\<close> where
  \<open>MICRO_RUST_SSA_CONTROL x \<equiv> x\<close>

method micro_rust_ssa_normalize =
  (rewrite at "\<hole> = _" MICRO_RUST_SSA_CONTROL_def[symmetric], \<comment> \<open>Add the constant on the LHS\<close>
    clarsimp simp only: micro_rust_ssa,                      \<comment> \<open>Simplify the expression\<close>
    (simp only: MICRO_RUST_SSA_CONTROL_def bind_assoc)?)     \<comment> \<open>Remove the constant\<close>

text\<open>We want the SSA transformations to operate as closely to the syntactic level as possible.
In fact, we could express them entirely at the syntax level, but they would not be provably correct
this way, but rather part of the definition of the denotational semantics.

One possible way around this could be to define SSA at the level of the abstract syntax, and apply
it automatically at every use of the shallow embedding bracket  \<^verbatim>\<open>\<lbrakk> _ \<rbrakk>\<close>, proving in the background
that the resulting shallowly  embedded expressions are indeed semantically equivalent. Since the
correctness proofs for the SSA transformations should be trivial, that should not require user
intervention. In other words, the SSA transformations would be proven to be correct on a
case-by-case basis.

To not stray afar, though, we use a middle ground below: We refer to the abstract Micro Rust syntax
for the constructions to be simplified, but use HOL antiquotations for the arguments.\<close>

lemma ssa_transform_funcall1 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>f\<close>(\<epsilon>\<open>e\<close>) \<rbrakk> =
            \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; \<epsilon>\<open>f\<close>(x0) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close>(\<epsilon>\<open>e\<close>,\<epsilon>\<open>f\<close>) \<rbrakk> =
            \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
              let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              \<epsilon>\<open>fn\<close> (x0, x1) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>) \<rbrakk> =
           \<lbrakk> let v0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let v1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let v2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
               \<epsilon>\<open>fn\<close>(v0,v1,v2) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
                \<epsilon>\<open>fn\<close>(x0,x1,x2,x3) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
             let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
             let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
             let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
             let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
             let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
             let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall9 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>,\<epsilon>\<open>e8\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
             let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
             let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
             let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
             let x8 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e8\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7,x8) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_funcall10 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>,\<epsilon>\<open>e8\<close>,\<epsilon>\<open>e9\<close>) \<rbrakk> =
           \<lbrakk> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
             let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
             let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
             let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
             let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
             let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
             let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
             let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
             let x8 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e8\<close>;
             let x9 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e9\<close>;
               \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_function_body [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (FunctionBody e) = FunctionBody (MICRO_RUST_SSA_CONTROL e)\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

lemma ssa_transform_call [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (call f) = call (MICRO_RUST_SSA_CONTROL f)\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

lemma ssa_transform_lambda [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> |t| { \<epsilon>\<open>b\<close> } \<rbrakk> = \<lbrakk> |t| { \<epsilon>\<open>MICRO_RUST_SSA_CONTROL b\<close> } \<rbrakk>\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

lemma ssa_transform_lambda_hol [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (\<lambda>v. b v) = (\<lambda>v. (MICRO_RUST_SSA_CONTROL (b v)))\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

text\<open>We hoist the expression to be returned out of the \<^verbatim>\<open>return\<close> expression, simplify it recursively
and bind it to a variable.  We then return that variable:\<close>
lemma ssa_transform_return [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> return \<epsilon>\<open>r\<close>; \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL r\<close>; return x; \<rbrakk>\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def return_func_def micro_rust_simps)

text\<open>The \<^term>\<open>MICRO_RUST_SSA_CONTROL\<close> marker commutes with the  \<^verbatim>\<open>let\<close> construct, entering both the
body and the bound expression, simplifying both recursively:\<close>
lemma ssa_transform_let_in [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind e f) =
          bind (MICRO_RUST_SSA_CONTROL e) (\<lambda>x. MICRO_RUST_SSA_CONTROL (f x))\<close>
  by (auto simp add: MICRO_RUST_SSA_CONTROL_def)

text\<open>The \<^term>\<open>MICRO_RUST_SSA_CONTROL\<close> marker commutes with the sequencing operator, entering the
two sequenced expressions and recursively transforming them.  Note that this is essentially a
corollary of the rule for ``let in'' as sequencing is a degenerate form of \<^verbatim>\<open>let\<close>:\<close>
corollary ssa_transform_sequence [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (sequence s t) = 
          sequence (MICRO_RUST_SSA_CONTROL s) (MICRO_RUST_SSA_CONTROL t)\<close>
  by (auto simp add: sequence_def bind_def MICRO_RUST_SSA_CONTROL_def)

text\<open>Since these lemmas are not expressible in terms of abstract Micro Rust, we probably don't want
them as part of \<^text>\<open>micro_rust_ssa\<close>?\<close>

lemma ssa_transform_lift1 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bindlift1 fn e) = 
            (let x = MICRO_RUST_SSA_CONTROL e; 
               bindlift1 fn (\<up>x))\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def micro_rust_simps)

lemma ssa_transform_bind2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind2 exp e f) =
            (let x0 = MICRO_RUST_SSA_CONTROL e;
             let x1 = MICRO_RUST_SSA_CONTROL f;
               (bind2 exp (\<up>x0) (\<up>x1)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind3 exp x0 x1 x2) =
            (let v0 = MICRO_RUST_SSA_CONTROL x0;
             let v1 = MICRO_RUST_SSA_CONTROL x1;
             let v2 = MICRO_RUST_SSA_CONTROL x2;
                (bind3 exp (\<up>v0) (\<up>v1) (\<up>v2)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind4 exp x0 x1 x2 x3) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
               (bind4 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind5 exp x0 x1 x2 x3 x4) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
               (bind5 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind6 exp x0 x1 x2 x3 x4 x5) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
               (bind6 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind7 exp x0 x1 x2 x3 x4 x5 x6) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
             let x6 = MICRO_RUST_SSA_CONTROL x6;
                (bind7 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5) (\<up>x6)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind8 exp x0 x1 x2 x3 x4 x5 x6 x7) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
             let x6 = MICRO_RUST_SSA_CONTROL x6;
             let x7 = MICRO_RUST_SSA_CONTROL x7;
                (bind8 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5) (\<up>x6) (\<up>x7)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)


subsection\<open>Single static assignment form for \<^emph>\<open>Range\<close>\<close>

lemma ssa_transform_range_is_empty [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (r\<cdot>is_empty\<langle>\<rangle>) \<rbrace> = \<lbrace>
           let x = MICRO_RUST_SSA_CONTROL r; (\<up>x)\<cdot>is_empty\<langle>\<rangle> \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_range_contains [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (r\<cdot>contains\<langle>x\<rangle>) \<rbrace> =
          \<lbrace> let r = MICRO_RUST_SSA_CONTROL r;
            let x = MICRO_RUST_SSA_CONTROL x;
             (\<up>r)\<cdot>contains\<langle>\<up>x\<rangle> \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_range_new [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (\<langle>b\<dots>e\<rangle>) \<rbrace> = \<lbrace>
            let x = MICRO_RUST_SSA_CONTROL b;
            let y = MICRO_RUST_SSA_CONTROL e;
             \<langle>(\<up>x) \<dots> (\<up>y)\<rangle> \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_range_eq_new [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (\<langle>b\<dots>=e\<rangle>) \<rbrace> = \<lbrace>
            let x = MICRO_RUST_SSA_CONTROL b;
            let y = MICRO_RUST_SSA_CONTROL e;
             \<langle>(\<up>x) \<dots>= (\<up>y)\<rangle> \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)


subsection\<open>Single static assignment form for \<^emph>\<open>Option\<close>\<close>

text\<open>TODO: should apply more generally to any match expression? The transformation below is not only
specific to the Option type, but also to the order of constructors given.\<close>
lemma ssa_transform_option_cases [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> match \<epsilon>\<open>e\<close> {
                                    None \<Rightarrow> \<epsilon>\<open>n\<close>,
                                    Some(s) \<Rightarrow> \<epsilon>\<open>sm s\<close>
                                  }\<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            match x {
               None \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL n\<close>,
               Some(s) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (sm s)\<close>
            }\<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_option_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_option exp) =
         \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL exp\<close>;
           match x {
             None \<Rightarrow> \<epsilon>\<open>return \<up>None\<close>,
             Some (s) \<Rightarrow> s
           } \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_option_def
    by (clarsimp simp add: micro_rust_simps)

subsection\<open>Single static assignment form for \<^emph>\<open>Result\<close>\<close>

text\<open>We extend the transformation of expressions into an SSA form to the operations on the \<^verbatim>\<open>Result\<close>
type, here.

TODO: should apply more generally to any match expression? The transformation below is not only
specific to the Result type, but also to the order of constructors given.  A similar problem exists
above for \<^verbatim>\<open>Option\<close>, too.\<close>
lemma ssa_transform_result_cases [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> match \<epsilon>\<open>e\<close> {
                                    Ok(x) \<Rightarrow> \<epsilon>\<open>ok x\<close>,
                                    Err(y) \<Rightarrow> \<epsilon>\<open>err y\<close>
                                  }\<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            match x {
               Ok(x) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (ok x)\<close>,
               Err(y) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (err y)\<close>
            }\<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_result_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_result exp) =
         \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL exp\<close>;
           match x {
             Err(e) \<Rightarrow> \<epsilon>\<open>return \<up>(Err e)\<close>,
             Ok (a) \<Rightarrow> a
           } \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_result_def
    by (clarsimp simp add: micro_rust_simps)


subsection\<open>Single static assignment form for \<^emph>\<open>Bool\<close>\<close>

lemma ssa_transform_assert [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert e) = \<lbrace> let x = MICRO_RUST_SSA_CONTROL e; assert (\<up>x) \<rbrace>\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def assert_def micro_rust_simps)

lemma ssa_transform_assert_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> assert_eq!(\<epsilon>\<open>e\<close>, \<epsilon>\<open>f\<close>) \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              assert_eq!(x,  y) 
           \<rbrakk>\<close>
unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; clarsimp simp add: bind2_def
  assert_eq_def bind_literal_unit)

subsection\<open>Single static assignment form for numeric and bitwise operators\<close>

lemma ssa_transform_HOL_if [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (if b then e else f) =
    (if b then MICRO_RUST_SSA_CONTROL e else MICRO_RUST_SSA_CONTROL f)\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

text\<open>It is rather unfortunate that we have to do this, but there is no generic way to write those
simplifications: case expressions are only syntactic sugar, and are elaborated into type-specific
expressions during parsing.\<close>

lemma ssa_transform_option [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (case_option f g x) =
          case_option (MICRO_RUST_SSA_CONTROL f) (MICRO_RUST_SSA_CONTROL g) x\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by auto

lemma ssa_transform_result [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (case_result f g x) =
          case_result (MICRO_RUST_SSA_CONTROL f) (MICRO_RUST_SSA_CONTROL g) x\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by auto 

text\<open>The following rules seem more suitable because they restrict to \<^verbatim>\<open>\<mu>Rust\<close> match constructs
rather than general case expressions. However, since the \<^verbatim>\<open>\<mu>Rust\<close> match construct is defined as a
bind with an anonymous HOL case, SSA simplification might step into the bind first, in which case we
end up with a nested HOL lambda and case:\<close>

lemma ssa_transform_option_urust [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> match \<epsilon>\<open>e\<close> {
            Some (v) \<Rightarrow> \<epsilon>\<open>case_some v\<close>,
            None \<Rightarrow> \<epsilon>\<open>case_none\<close>
         } \<rbrakk> = 
         \<lbrakk> let ve = \<epsilon>\<open>e\<close>;
           match ve {
             Some (v) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (case_some v)\<close>,
             None \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL case_none\<close>
           } \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind_literal_unit)

lemma ssa_transform_result_urust [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> match \<epsilon>\<open>e\<close> {
            Ok (v) \<Rightarrow> \<epsilon>\<open>case_ok v\<close>,
            Err (v) \<Rightarrow> \<epsilon>\<open>case_err v\<close>
         } \<rbrakk> = 
         \<lbrakk> let ve = \<epsilon>\<open>e\<close>;
           match ve {
             Ok (v) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (case_ok v)\<close>,
             Err (v) \<Rightarrow> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (case_err v)\<close>
           } \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind_literal_unit)

lemma ssa_transform_HOL_case_prod [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (case t of (a,b) \<Rightarrow> e a b) =
    (case t of (a,b) \<Rightarrow> MICRO_RUST_SSA_CONTROL (e a b))\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def)

lemma ssa_transform_let [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> let x = \<epsilon>\<open>e\<close>; \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close> \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; elim micro_rust_elims;
      clarsimp; intro micro_rust_intros;
      clarsimp simp add: micro_rust_simps; force)

lemma ssa_transform_to_unit [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close>; \<rbrakk> =
          \<lbrakk> \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; elim micro_rust_elims;
      clarsimp; intro micro_rust_intros;
      clarsimp simp add: micro_rust_simps; force)

lemma ssa_transform_two_armed_conditional [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL 
    \<lbrakk> if \<epsilon>\<open>condition_exp\<close> { 
         \<epsilon>\<open>true_branch\<close> 
      } else { 
         \<epsilon>\<open>false_branch\<close> 
      } \<rbrakk> =
    \<lbrakk> let condition_val = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL condition_exp\<close>;
      if condition_val { 
         \<epsilon>\<open>MICRO_RUST_SSA_CONTROL true_branch\<close> 
      } else { 
         \<epsilon>\<open>MICRO_RUST_SSA_CONTROL false_branch\<close> 
      } 
    \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; elim micro_rust_elims;
      clarsimp; intro micro_rust_intros;
      clarsimp simp add: micro_rust_simps two_armed_conditional_def; force)

corollary ssa_transform_one_armed_conditional:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> if ( \<epsilon>\<open>e\<close>) { \<epsilon>\<open>t\<close> } \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; if (x) { \<epsilon>\<open>MICRO_RUST_SSA_CONTROL t\<close> } \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by(metis MICRO_RUST_SSA_CONTROL_def ssa_transform_two_armed_conditional)

lemma ssa_transform_boolean_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> !\<epsilon>\<open>e :: ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             !x \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps negation_def)

lemma ssa_transform_binary_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> !\<epsilon>\<open>e :: ('s, 64 word, 'r, 'abort, 'i, 'o) expression\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             !x \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_not_pure_def
                                              word_bitwise_not_def)

lemma ssa_transform_binary_or [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> | \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x | y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_or_pure_def
                                              word_bitwise_or_def)

lemma ssa_transform_add [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> + \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x + y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_add_no_wrap_def)

lemma ssa_transform_minus [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> - \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x - y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_minus_no_wrap_def)

lemma ssa_transform_mul [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> * \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x * y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_mul_no_wrap_def)

lemma ssa_transform_div [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> / \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x / y
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_udiv_def)

lemma ssa_transform_mod [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> % \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x % y
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_umod_def)

lemma ssa_transform_binary_xor [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> ^ \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x ^ y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

lemma ssa_transform_binary_and [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> & \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x & y 
           \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

lemma ssa_transform_word_shift_left [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> << \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x << y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_left_shift64_def word_shift_left_def)

lemma ssa_transform_word_shift_right [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> >> \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x >> y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_right_shift64_def word_shift_right_def)

lemma ssa_transform_urust_neq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> != \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x != y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_neq_def)

lemma ssa_transform_urust_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> == \<epsilon>\<open>f\<close> \<rbrakk> =
           \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
             let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              x == y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_eq_def)

lemma ssa_transform_urust_disj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> || \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            if x { True } else { 
              let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              y } \<rbrakk>\<close> 
  by (simp add: urust_disj_def micro_rust_simps MICRO_RUST_SSA_CONTROL_def
    two_armed_conditional_def) (meson true_def)

lemma ssa_transform_urust_conj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> && \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            if x {
              let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
              y
            } else { False } \<rbrakk>\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def micro_rust_simps urust_conj_def
    two_armed_conditional_def) (meson false_def)

lemma ssa_transform_urust_ge [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> >= \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
            x >= y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_ge_def) 

lemma ssa_transform_urust_le [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> <= \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
            x <= y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_le_def) 

lemma ssa_transform_urust_gt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> > \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
            x > y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_gt_def) 

lemma ssa_transform_urust_lt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL \<lbrakk> \<epsilon>\<open>e\<close> < \<epsilon>\<open>f\<close> \<rbrakk> =
          \<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
            let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
            x < y \<rbrakk>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_lt_def) 

subsection\<open>Single static assignment form for loops\<close>

lemma ssa_transform_for_loop [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (for_loop i body) \<rbrace> = 
         \<lbrace> let x = MICRO_RUST_SSA_CONTROL i;
           for_loop (literal x) (\<lambda>idx. MICRO_RUST_SSA_CONTROL (body idx)) \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind_literal_unit for_loop_def)

(*<*)
end
(*>*)
