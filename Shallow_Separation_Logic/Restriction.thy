(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Restriction
  imports Precision
begin

context sepalg begin
(*>*)

text\<open>The goal of this section is to define a general notion of
restriction and complement which is uniquely defined and well-behaved in general, and specializes
(in a precise sense) to the components of a minimal splitting, in case the latter exists.

The idea for defining restriction and complement in general is to identify states \<^term>\<open>\<sigma>\<close>
with their upwards or downwards closures \<^term>\<open>\<up>\<^sub>s \<sigma>\<close> and \<^term>\<open>\<down>\<^sub>s \<sigma>\<close> (which determine \<^term>\<open>\<sigma>\<close> up to
\<^term>\<open>(\<preceq>)\<close>-equivalence), and to observe that in the case of the components of a minimal
decomposition, their upward resp. downward closures can be written down explicitly in terms of
\<^term>\<open>\<sigma>\<close> and \<^term>\<open>\<xi>\<close> \<^emph>\<open>even if\<close> the minimal decomposition itself does not exist.

The idea of describing state not explicitly but in terms of derived data is commonly found in mathematics:
For example, the through of an ideal (for "ideal number") in ring theory one operates on numbers in terms of
their sets of multiples, sometimes giving notions of e.g. unique factorization where they don't exist in the
classical sense. Our approach here is very similar in spirit.\<close>

text\<open>The following formalizes the restriction of a state with respect to an assertion,
\<^emph>\<open>as an assertion\<close>:\<close>

definition arestrict :: \<open>'a \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> (infix "|\<^sub>R" 60)  where
  \<open>\<sigma> |\<^sub>R \<xi> \<equiv> {\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<xi> \<and> \<tau> \<preceq> \<sigma> \<and> \<tau> \<preceq> \<sigma>'}\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma ucincl_arestrict:
  shows \<open>ucincl (\<sigma> |\<^sub>R \<xi>)\<close>
by (clarsimp simp add: arestrict_def intro!: ucinclI ucpredI) (meson local.derived_order_trans)

text\<open>The restriction is only meaningful if the input state satisfies the given assertion.\<close>

lemma arestrict_outside:
  assumes \<open>\<not> \<sigma> \<Turnstile> \<xi>\<close>
     and \<open>ucincl \<xi>\<close>
   shows \<open>\<sigma> |\<^sub>R \<xi> = \<bottom>\<close>
using arestrict_def assms asat_derived_order_monotone by auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma arestrict_alt:
  shows \<open>\<sigma> |\<^sub>R \<phi> = (\<Squnion>\<tau> \<in> (\<down>\<^sub>s \<sigma> \<sqinter> \<phi>). \<up>\<^sub>s \<tau>)\<close>
    and \<open>\<sigma> |\<^sub>R \<phi> = (\<down>\<^sub>s \<sigma> \<sqinter> \<phi>) \<star> \<top>\<close>
proof -
  have \<open>{\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<phi> \<and> \<tau> \<preceq> \<sigma> \<and> \<tau> \<preceq> \<sigma>'} = (\<Union>x\<in>{\<sigma>'. \<sigma>' \<preceq> \<sigma>} \<inter> \<phi>. {\<sigma>'. x \<preceq> \<sigma>'})\<close>
    by (auto simp add: asat_def)
  from this show \<open>\<sigma> |\<^sub>R \<phi> = (\<Squnion>\<tau> \<in> (\<down>\<^sub>s \<sigma> \<sqinter> \<phi>). \<up>\<^sub>s \<tau>)\<close>
    by (clarsimp simp add: arestrict_def uc_state_def dc_state_def)
  from this show \<open>\<sigma> |\<^sub>R \<phi> = (\<down>\<^sub>s \<sigma> \<sqinter> \<phi>) \<star> \<top>\<close>
    using uc_state_alt by presburger
qed

text\<open>Given a \<^term>\<open>\<sigma>\<close> with \<^term>\<open>\<sigma> \<Turnstile> \<xi>\<close> and a substate \<^term>\<open>\<tau> \<preceq> \<sigma>\<close> with \<^term>\<open>\<tau> \<Turnstile> \<xi>\<close>,
one would intuitively expect that the restrictions of \<^term>\<open>\<sigma>\<close> and \<^term>\<open>\<tau>\<close> to \<^term>\<open>\<xi>\<close>
should coincide. This, however, is only true under a mild technical assumption which
we call "intersection stability":\<close>

definition is_intersection_stable :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>is_intersection_stable \<xi> \<equiv>
     ucincl \<xi> \<and> (\<forall>\<alpha> \<beta> \<gamma>. \<alpha> \<Turnstile> \<xi> \<longrightarrow> \<beta> \<Turnstile> \<xi> \<longrightarrow> \<alpha> \<preceq> \<gamma> \<longrightarrow> \<beta> \<preceq> \<gamma> \<longrightarrow> (\<exists>\<rho>. \<rho> \<Turnstile> \<xi> \<and> \<rho> \<preceq> \<alpha> \<and> \<rho> \<preceq> \<beta>))\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma is_intersection_stableI:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<And>\<alpha> \<beta> \<gamma>. \<alpha> \<Turnstile> \<xi> \<Longrightarrow> \<beta> \<Turnstile> \<xi> \<Longrightarrow> \<alpha> \<preceq> \<gamma> \<Longrightarrow> \<beta> \<preceq> \<gamma> \<Longrightarrow> \<exists>\<rho>. \<rho> \<Turnstile> \<xi> \<and> \<rho> \<preceq> \<alpha> \<and> \<rho> \<preceq> \<beta>\<close>
    shows \<open>is_intersection_stable \<xi>\<close>
using assms by (auto simp add: is_intersection_stable_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma is_intersection_stableE:
  assumes \<open>is_intersection_stable \<xi>\<close>
      and \<open>ucincl \<xi> \<Longrightarrow> (\<And>\<alpha> \<beta> \<gamma>. \<alpha> \<Turnstile> \<xi> \<Longrightarrow> \<beta> \<Turnstile> \<xi> \<Longrightarrow> \<alpha> \<preceq> \<gamma> \<Longrightarrow> \<beta> \<preceq> \<gamma> \<Longrightarrow> \<exists>\<rho>. \<rho> \<Turnstile> \<xi> \<and> \<rho> \<preceq> \<alpha> \<and> \<rho> \<preceq> \<beta>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: is_intersection_stable_def)

lemma has_minimal_splittings_implies_intersection_stable:
  assumes \<open>has_minimal_splittings \<xi>\<close>
    shows \<open>is_intersection_stable \<xi>\<close>
  using assms by (auto simp add: has_minimal_splittings_def is_intersection_stable_def is_minimal_splitting_def
    is_splitting_def) (metis local.asat_weaken local.derived_order_def)

lemma arestrict_restrict:
  assumes \<open>is_intersection_stable \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close> and \<open>\<tau> \<Turnstile> \<xi>\<close> and \<open>\<tau> \<preceq> \<sigma>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> = \<tau> |\<^sub>R \<xi>\<close> (is \<open>?a = ?b\<close>)
proof -
  have \<open>?b \<subseteq> ?a\<close>
    using assms by (clarsimp simp add: arestrict_def is_intersection_stable_def asat_def)
      (meson local.derived_order_trans)
  {
       fix \<alpha>
    assume \<open>\<alpha> \<Turnstile> \<sigma> |\<^sub>R \<xi>\<close>
    from this obtain \<rho> where \<open>\<rho> \<Turnstile> \<xi>\<close> and \<open>\<rho> \<preceq> \<sigma>\<close> and \<open>\<rho> \<preceq> \<alpha>\<close>
      by (auto simp add: arestrict_def asat_def)
    moreover from this and \<open>is_intersection_stable \<xi>\<close> obtain \<rho>' where \<open>\<rho>' \<preceq> \<rho>\<close> and \<open>\<rho>' \<preceq> \<tau>\<close> and \<open>\<rho>' \<Turnstile> \<xi>\<close>
      by (meson is_intersection_stable_def assms(3) assms(4))
    ultimately have \<open>\<alpha> \<Turnstile> \<tau> |\<^sub>R \<xi>\<close>
      by (clarsimp simp add: arestrict_def asat_def) (meson local.derived_order_trans)
  }
  from this have \<open>?a \<subseteq> ?b\<close>
    by (simp add: asat_def subsetI)
  show ?thesis
    using \<open>\<sigma> |\<^sub>R \<xi> \<subseteq> \<tau> |\<^sub>R \<xi>\<close> \<open>\<tau> |\<^sub>R \<xi> \<subseteq> \<sigma> |\<^sub>R \<xi>\<close> by blast
qed

lemma arestrict_rigid:
  assumes \<open>is_intersection_stable \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>\<sigma>' \<Turnstile> \<xi>\<close>
      and \<open>\<sigma>' |\<^sub>R \<xi> \<subseteq> \<sigma> |\<^sub>R \<xi>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> = \<sigma>' |\<^sub>R \<xi>\<close>
proof -
  have \<open>\<sigma>' \<Turnstile> \<sigma>' |\<^sub>R \<xi>\<close>
    using arestrict_def asat_def assms(3) by fastforce
  from this and assms have \<open>\<sigma>' \<Turnstile> \<sigma> |\<^sub>R \<xi>\<close>
    by (simp add: asat_def subset_iff)
  from this obtain \<rho> where \<open>\<rho> \<Turnstile> \<xi>\<close> and \<open>\<rho> \<preceq> \<sigma>\<close> and \<open>\<rho> \<preceq> \<sigma>'\<close>
    by (auto simp add: arestrict_def asat_def)
  from this show ?thesis
    by (metis arestrict_restrict assms(1) assms(2) assms(3))
qed

lemma arestrict_mono:
  assumes \<open>\<xi> \<longlongrightarrow> \<pi>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> \<longlongrightarrow> \<sigma>|\<^sub>R \<pi>\<close>
using assms by (auto simp add: arestrict_def aentails_def asat_def)

lemma arestrict_idempotent:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>is_intersection_stable \<xi>\<close>
      and \<open>\<sigma>' \<Turnstile> \<sigma> |\<^sub>R \<xi>\<close>
      and \<open>\<sigma>'' \<Turnstile> \<sigma>' |\<^sub>R \<xi>\<close>
    shows \<open>\<sigma>'' \<Turnstile> \<sigma> |\<^sub>R \<xi>\<close>
proof -
  from assms obtain \<tau> \<tau>' where \<open>\<tau> \<Turnstile> \<xi>\<close> and \<open>\<tau>' \<Turnstile> \<xi>\<close> and \<open>\<tau> \<preceq> \<sigma>\<close> and \<open>\<tau> \<preceq> \<sigma>'\<close> and \<open>\<tau>' \<preceq> \<sigma>'\<close> and \<open>\<tau>' \<preceq> \<sigma>''\<close>
    by (clarsimp simp add: arestrict_def asat_def)
  from this and \<open>is_intersection_stable \<xi>\<close> show ?thesis
    using assms by (metis arestrict_restrict local.asat_derived_order_monotone)
qed

corollary arestrict_idempotent':
  assumes \<open>ucincl \<xi>\<close>
      and \<open>is_intersection_stable \<xi>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> = (\<Squnion>\<sigma>'\<in> \<sigma> |\<^sub>R \<xi>. \<sigma>' |\<^sub>R \<xi>)\<close> (is \<open>?a = ?b\<close>)
proof -
  {
    assume \<open>\<not> \<sigma> \<Turnstile> \<xi>\<close>
    from this have \<open>?a = ?b\<close>
      using arestrict_outside assms by auto
  }
  moreover {
    assume \<open>\<sigma> \<Turnstile> \<xi>\<close>
    from assms have \<open>?b \<subseteq> ?a\<close>
      using arestrict_idempotent by (auto simp add: asat_def)
    moreover have \<open>\<sigma> \<in> \<sigma> |\<^sub>R \<xi>\<close>
      using \<open>\<sigma> \<Turnstile> \<xi>\<close> arestrict_def by auto
    moreover from this have \<open>?a \<subseteq> ?b\<close>
      by blast
    ultimately have \<open>?a = ?b\<close>
      by auto
  }
  ultimately show ?thesis
    by auto
qed

lemma arestrict_trans:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<pi> \<longlongrightarrow> \<xi>\<close>
      and \<open>is_intersection_stable \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<pi>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> = (\<Squnion>\<sigma>'\<in> \<sigma> |\<^sub>R \<pi>. \<sigma>' |\<^sub>R \<xi>)\<close> (is \<open>?a = ?b\<close>)
proof -
  have \<open>?b \<subseteq> (\<Squnion>\<sigma>'\<in> \<sigma> |\<^sub>R \<xi>. \<sigma>' |\<^sub>R \<xi>)\<close>
    using assms arestrict_mono by (metis SUP_mono aentailsE asat_def set_eq_subset)
  from this have \<open>?b \<subseteq> ?a\<close>
    using arestrict_idempotent' assms by auto
  moreover have \<open>\<sigma> \<Turnstile> \<sigma> |\<^sub>R \<pi>\<close>
    using arestrict_def asat_def assms(4) by fastforce
  moreover from this have \<open>?a \<subseteq> ?b\<close>
    by (simp add: SUP_upper2 asat_def)
  ultimately show ?thesis
    by auto
qed

corollary arestrict_eq_trans:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<pi> \<longlongrightarrow> \<xi>\<close>
      and \<open>is_intersection_stable \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<pi>\<close> and \<open>\<sigma>' \<Turnstile> \<pi>\<close>
      and \<open>\<sigma> |\<^sub>R \<pi> = \<sigma>' |\<^sub>R \<pi>\<close>
    shows \<open>\<sigma> |\<^sub>R \<xi> = \<sigma>' |\<^sub>R \<xi>\<close>
using assms arestrict_trans by auto

text\<open>Next, we can define the notion of \<^emph>\<open>complement\<close> of a state with respect to an assertion:\<close>

definition awithout :: \<open>'a \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> ("_\\_" [100,100]51) where
  \<open>\<sigma> \ \<xi> \<equiv> {\<sigma>'. \<exists>\<tau> \<sigma>''. \<tau> \<Turnstile> \<xi> \<and> \<tau> \<sharp> \<sigma>'' \<and> \<tau> + \<sigma>'' = \<sigma> \<and> \<sigma>' \<preceq> \<sigma>''}\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma awithout_alt:
  assumes \<open>ucincl \<xi>\<close>
    shows \<open>\<sigma> \ \<xi> = {\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<xi> \<and> \<tau> \<sharp> \<sigma>' \<and> \<tau> + \<sigma>' = \<sigma>}\<close>
proof -
  {
       fix x \<tau> z
    assume \<open>\<tau> \<Turnstile> \<xi>\<close>
       and \<open>\<tau> \<sharp> x + z\<close>
       and \<open>\<sigma> = \<tau> + (x + z)\<close>
       and \<open>x \<sharp> z\<close>
    from this assms have \<open>\<exists>\<tau>'. \<tau>' \<Turnstile> \<xi> \<and> x \<sharp> \<tau>' \<and> \<tau>' + x = \<tau> + (x + z)\<close>
      by (metis local.asat_weaken2 local.disjoint_sym local.sepalg_apart_assoc local.sepalg_apart_plus2
        local.sepalg_assoc local.sepalg_comm)
  } moreover {
       fix x \<tau>
    assume \<open>\<tau> \<Turnstile> \<xi>\<close>
       and \<open>x \<sharp> \<tau>\<close>
       and \<open>\<sigma> = x + \<tau>\<close>
    from this have \<open>\<exists>\<tau>'. \<tau>' \<Turnstile> \<xi> \<and> (\<exists>\<sigma>''. \<tau>' \<sharp> \<sigma>'' \<and> \<tau>' + \<sigma>'' = x + \<tau> \<and> (\<exists>z. x \<sharp> z \<and> x + z = \<sigma>''))\<close>
      by force
  }
  ultimately have \<open>{\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<xi> \<and> (\<exists>\<sigma>''. \<tau> \<sharp> \<sigma>'' \<and> \<tau> + \<sigma>'' = \<sigma> \<and> (\<exists>z. \<sigma>' \<sharp> z \<and> \<sigma>' + z = \<sigma>''))} = {\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<xi> \<and> \<sigma>' \<sharp> \<tau> \<and> \<tau> + \<sigma>' = \<sigma>}\<close>
    by (metis (no_types, opaque_lifting) local.disjoint_sym local.sepalg_ident2 local.zero_disjoint)
  from this show \<open>\<sigma> \ \<xi> = {\<sigma>'. \<exists>\<tau>. \<tau> \<Turnstile> \<xi> \<and> \<tau> \<sharp> \<sigma>' \<and> \<tau> + \<sigma>' = \<sigma>}\<close>
    by (clarsimp simp add: ucincl_def ucpred_def awithout_def derived_order_def)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma dcincl_awithout:
  shows \<open>dcincl (\<sigma> \ \<xi>)\<close>
by (clarsimp simp add: dcincl_def dcpred_def awithout_def derived_order_def) (metis
  local.disjoint_sym local.sepalg_apart_assoc local.sepalg_apart_plus2 local.sepalg_assoc
  local.sepalg_comm)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma arestrict_rigid_basic:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>\<close>
      and \<open>is_minimal_splitting \<sigma>' \<sigma>\<^sub>1' \<sigma>\<^sub>2' \<xi>\<close>
      and \<open>\<sigma>\<^sub>1 \<preceq> \<sigma>\<^sub>1'\<close>
    shows \<open>\<sigma>\<^sub>1' \<preceq> \<sigma>\<^sub>1\<close>
using assms by (clarsimp simp add: is_minimal_splitting_def is_splitting_def) (metis
  local.derived_order_def local.derived_order_trans)

lemma awithout_via_upwards_closure:
  shows \<open>(\<sigma> \ \<xi>) = { \<rho>. \<sigma> \<Turnstile> \<up>\<^sub>s \<rho> \<star> \<xi> }\<close>
proof -
  have \<open>\<sigma> \ \<xi> \<longlongrightarrow> { \<rho>. \<sigma> \<Turnstile> \<up>\<^sub>s \<rho> \<star> \<xi> }\<close>
    by (clarsimp simp add: awithout_def aentails_def asat_def uc_state_def) (metis asat_def
      local.asepconjI local.asepconj_comm mem_Collect_eq)
  moreover have \<open>{ \<rho>. \<sigma> \<Turnstile> \<up>\<^sub>s \<rho> \<star> \<xi> } \<longlongrightarrow> \<sigma> \ \<xi>\<close>
    by (clarsimp simp add: awithout_def aentails_def asat_def uc_state_def) (metis asat_def
      local.asepconjE local.asepconj_comm mem_Collect_eq)
  ultimately show ?thesis
    using aentails_eq by auto
qed

lemma ucincl_assert_as_union_of_upwards_closures:
  assumes \<open>ucincl \<pi>\<close>
    shows \<open>\<pi> = (\<Squnion>\<sigma>\<in>\<pi>. \<up>\<^sub>s \<sigma>)\<close> (is \<open>?a = ?b\<close>)
proof -
  have A: \<open>?a \<subseteq> ?b\<close>
    using assms aentails_uc[simplified aentails_def] uc_state_def by auto
  {
       fix \<sigma>
    assume \<open> \<sigma> \<in> \<pi>\<close>
    from this have \<open>\<up>\<^sub>s \<sigma> \<subseteq> \<pi>\<close>
      using assms local.ucincl_def local.ucpred_def uc_state_def by auto
  }
  from this have B: \<open>?b \<subseteq> ?a\<close>
    by blast
  from A B show ?thesis
    by auto
qed

text\<open>The following lemma justifies our construction: We show that, for assertions with minimal
splittings, \<^text>\<open>\<sigma>|\<xi>\<close> and \<^text>\<open>\<sigma>\\<xi>\<close> indeed recover (the upwards and downwards closures of) the
components of a minimal splitting.\<close>

lemma
  assumes \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>\<close>
    shows \<open>\<up>\<^sub>s \<sigma>\<^sub>1 = \<sigma> |\<^sub>R \<xi>\<close>
      and \<open>\<down>\<^sub>s \<sigma>\<^sub>2 = (\<sigma> \ \<xi>)\<close>
proof -
  have \<open>\<up>\<^sub>s \<sigma>\<^sub>1 \<longlongrightarrow> \<sigma> |\<^sub>R \<xi>\<close>
    using assms by (fastforce simp add: aentails_def derived_order_def arestrict_def
        asat_def is_minimal_splitting_def is_splitting_def uc_state_def)
  {
       fix \<sigma>'
    assume \<open>\<sigma>' \<Turnstile> \<sigma> |\<^sub>R \<xi>\<close>
    from this arestrict_def obtain \<tau> where \<open>\<tau> \<Turnstile> \<xi>\<close> and \<open>\<tau> \<preceq> \<sigma>\<close> and \<open>\<tau> \<preceq> \<sigma>'\<close>
      by (clarsimp simp add: asat_def)
    from this obtain \<sigma>'' where \<open>is_splitting \<sigma> \<tau> \<sigma>''\<close>
      using is_splitting_def by blast
    from this \<open>\<tau> \<Turnstile> \<xi>\<close> is_minimal_splitting_def \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>\<close> have \<open>\<sigma>\<^sub>1 \<preceq> \<tau>\<close>
      by force
    from this and \<open>\<tau> \<preceq> \<sigma>'\<close> have \<open>\<sigma>' \<Turnstile> \<up>\<^sub>s \<sigma>\<^sub>1\<close> using derived_order_trans
      by (metis CollectI asat_def uc_state_def)
  }
  from this have \<open>\<sigma> |\<^sub>R \<xi> \<longlongrightarrow>  \<up>\<^sub>s \<sigma>\<^sub>1\<close>
    by (simp add: aentails_def)
  from \<open>\<up>\<^sub>s \<sigma>\<^sub>1 \<longlongrightarrow> \<sigma> |\<^sub>R \<xi>\<close> and \<open>\<sigma> |\<^sub>R \<xi> \<longlongrightarrow>  \<up>\<^sub>s \<sigma>\<^sub>1\<close> show \<open>\<up>\<^sub>s \<sigma>\<^sub>1 = \<sigma> |\<^sub>R \<xi>\<close>
    by (meson aentails_def asat_semequivI)
next
  have \<open>\<down>\<^sub>s \<sigma>\<^sub>2 \<longlongrightarrow> (\<sigma> \ \<xi>)\<close>
    by (clarsimp simp add: awithout_def derived_order_def asat_def assms dc_state_def aentails_def)
      (metis asat_def assms is_minimal_splitting_def is_splitting_def)
  {
       fix \<sigma>'
    assume \<open>\<sigma>' \<Turnstile> \<sigma> \ \<xi>\<close>
    from this arestrict_def obtain \<tau> \<sigma>'' where \<open>\<tau> \<Turnstile> \<xi>\<close> and \<open>\<tau> \<sharp> \<sigma>''\<close> and \<open>\<sigma>' \<preceq> \<sigma>''\<close> and \<open>\<tau> + \<sigma>'' = \<sigma>\<close>
      by (clarsimp simp add: asat_def awithout_def)
    from this have \<open>is_splitting \<sigma> \<tau> \<sigma>''\<close>
      using is_splitting_def by blast
    from this \<open>\<tau> \<Turnstile> \<xi>\<close> is_minimal_splitting_def \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>\<close> have \<open>\<sigma>'' \<preceq> \<sigma>\<^sub>2\<close>
      by blast
    from \<open>\<sigma>' \<preceq> \<sigma>''\<close> this have \<open>\<sigma>' \<preceq> \<sigma>\<^sub>2\<close> using derived_order_trans
      by blast
    from this have \<open>\<sigma>' \<Turnstile> \<down>\<^sub>s \<sigma>\<^sub>2\<close>
      by (simp add: asat_def dc_state_def)
  }
  from this have \<open>\<sigma> \ \<xi> \<longlongrightarrow>  \<down>\<^sub>s \<sigma>\<^sub>2\<close>
    by (simp add: aentails_def)
  from \<open>\<down>\<^sub>s \<sigma>\<^sub>2 \<longlongrightarrow> (\<sigma> \ \<xi>)\<close> and \<open>(\<sigma> \ \<xi>) \<longlongrightarrow>  \<down>\<^sub>s \<sigma>\<^sub>2\<close> show \<open>\<down>\<^sub>s \<sigma>\<^sub>2 = \<sigma> \ \<xi>\<close>
    by (meson aentails_def asat_semequivI)
qed

(*<*)
end

end
(*>*)