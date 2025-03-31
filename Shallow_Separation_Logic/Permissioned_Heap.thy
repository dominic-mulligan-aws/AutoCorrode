(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Permissioned_Heap
  imports Share_Map
begin
(*>*)

section\<open>A runtime heap\<close>

text\<open>This theory defines an efficient implementation of a "runtime heap" which can be
used to model, for example, mutable local variables.\<close>

datatype_record 'v mem_raw =
  memory_rbt_raw :: \<open>(nat, 'v) rbt_share_map\<close>
  memory_allocator_raw :: \<open>nat option\<close>

abbreviation memory_map_raw :: \<open>'v mem_raw \<Rightarrow> nat \<Rightarrow> 'v shareable_value\<close> where
  \<open>memory_map_raw mem \<equiv> rbt_share_map_\<alpha> (memory_rbt_raw mem)\<close>

definition mem_is_valid :: \<open>'v mem_raw \<Rightarrow> bool\<close> where
  \<open>mem_is_valid m \<equiv> \<forall>n. memory_allocator_raw m = Some n \<longrightarrow>
     (\<forall>a sh v. memory_map_raw m a = Shared_Value sh v \<longrightarrow> a < n)\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma mem_is_validI:
  assumes \<open>memory_allocator_raw m = Some n\<close>
      and \<open>\<And>a sh v. memory_map_raw m a = Shared_Value sh v \<Longrightarrow> a < n\<close>
    shows \<open>mem_is_valid m\<close>
using assms by (auto simp add: mem_is_valid_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma mem_is_validE:
  assumes \<open>mem_is_valid m\<close>
      and \<open>(\<And>n. memory_allocator_raw m = Some n \<Longrightarrow>
           (\<And>a sh v. memory_map_raw m a = Shared_Value sh v \<Longrightarrow> a < n)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: mem_is_valid_def)

typedef (overloaded) 'a mem = \<open>{ m :: 'a mem_raw . mem_is_valid m }\<close>
proof
  show \<open>(make_mem_raw 0 0) \<in> {m. mem_is_valid m}\<close>
    by (auto simp: mem_is_valid_def zero_fun_def)
qed

(*<*)
setup_lifting type_definition_mem
(*>*)

lift_definition memory_rbt :: \<open>'v mem \<Rightarrow> (nat, 'v) rbt_share_map\<close> is \<open>memory_rbt_raw\<close> .
lift_definition memory_allocator :: \<open>'v mem \<Rightarrow> nat option\<close> is \<open>memory_allocator_raw\<close> .

abbreviation (input) memory_map :: \<open>'v mem \<Rightarrow> nat \<Rightarrow> 'v shareable_value\<close> where
  \<open>memory_map mem \<equiv> rbt_share_map_\<alpha> (memory_rbt mem)\<close>

definition mem_alloc_pool :: \<open>'v mem \<Rightarrow> nat set\<close> where
  \<open>mem_alloc_pool m \<equiv> { x. \<exists>n. memory_allocator m = Some n \<and> x \<ge> n}\<close>

lift_definition initial_mem :: \<open>'v mem\<close> is
  \<open>make_mem_raw 0 (Some 0)\<close>
by (auto simp add: mem_is_valid_def zero_fun_def)

lemma init_mem_components [simp]:
  shows \<open>memory_allocator initial_mem = Some 0\<close>
    and \<open>mem_alloc_pool initial_mem = UNIV\<close>
    and \<open>memory_map initial_mem = (\<lambda>_. No_Value)\<close>
proof -
  show \<open>memory_allocator initial_mem = Some 0\<close>
    by transfer simp
  from this show \<open>mem_alloc_pool initial_mem = UNIV\<close>
    by (auto simp add: mem_alloc_pool_def)
  show \<open>memory_map initial_mem = (\<lambda>_. No_Value)\<close>
    by transfer (simp add: zero_fun_def)
qed

lemma mem_eqI:
  assumes \<open>memory_allocator m0 = memory_allocator m1\<close>
      and \<open>memory_rbt m0 = memory_rbt m1\<close>
    shows \<open>m0 = m1\<close>
using assms by transfer (simp add: mem_raw.expand)

definition dom_mem :: \<open>'v mem \<Rightarrow> nat set\<close> where
  \<open>dom_mem m \<equiv> sh_dom (memory_map m)\<close>

lemma mem_alloc_pool_dom_disjoint:
  shows \<open>dom_mem m \<inter> mem_alloc_pool m = {}\<close>
proof -
  have \<open>mem_is_valid (Rep_mem m)\<close>
    using Rep_mem by blast
  from this show ?thesis
    by (auto simp add: mem_is_valid_def dom_mem_def mem_alloc_pool_def memory_rbt_def
      memory_allocator_def disjoint_iff linorder_not_le sh_dom_def)
qed

definition mem_perm_map :: \<open>'v mem \<Rightarrow> nat \<Rightarrow> share\<close> where
  \<open>mem_perm_map m a \<equiv> shareable_value_to_share (memory_map m a)\<close>

definition mem_can_alloc :: \<open>'v mem \<Rightarrow> bool\<close> where
  \<open>mem_can_alloc m \<equiv> \<exists>n. memory_allocator m = Some n\<close>

instantiation mem :: (type)apart
begin

lift_definition zero_mem :: \<open>'a mem\<close> is
  \<open>make_mem_raw 0 None\<close>
by (clarsimp simp add: mem_is_valid_def)

lemma zero_mem_components:
  shows \<open>memory_allocator 0 = None\<close>
    and \<open>memory_rbt 0 = 0\<close>
    and \<open>mem_alloc_pool 0 = {}\<close>
proof -
  show \<open>memory_allocator 0 = None\<close> and \<open>memory_rbt 0 = 0\<close>
    by (transfer, simp add: zero_mem_def)+
  from this show \<open>mem_alloc_pool 0 = {}\<close>
    by (clarsimp simp add: mem_alloc_pool_def)
qed

lemma is_zero_memI:
    fixes x :: \<open>'v mem\<close>
  assumes \<open>memory_allocator x = None\<close>
      and \<open>memory_rbt x = 0\<close>
    shows \<open>x = 0\<close>
using assms by (intro mem_eqI; simp add: rbt_share_map_eqI zero_set_def zero_fun_def
  Permissioned_Heap.zero_mem_components)

definition disjoint_mem :: \<open>'v mem \<Rightarrow> 'v mem \<Rightarrow> bool\<close> where
  \<open>disjoint_mem m1 m2 \<longleftrightarrow>
     mem_alloc_pool m1 \<sharp> sh_dom (memory_map m2) \<and>
     sh_dom (memory_map m1) \<sharp> mem_alloc_pool m2 \<and>
     memory_rbt m1 \<sharp> memory_rbt m2 \<and>
     memory_allocator m1 \<sharp> memory_allocator m2\<close>

instance
proof
   fix x :: \<open>'a mem\<close>
  show \<open>x \<sharp> 0\<close>
    by (clarsimp simp add: zero_fun_def disjoint_mem_def disjoint_option_def disjoint_set_def
      zero_mem_components)
next
   fix x y :: \<open>'a mem\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (clarsimp simp add: disjoint_mem_def disjoint_set_def disjoint_fun_def disjoint_option_def
      split: option.splits) meson
next
     fix x :: \<open>'a mem\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (intro is_zero_memI; force simp add: zero_option_def disjoint_mem_def)
qed

end

context
begin

private definition mem_alloc_pool_raw :: \<open>'v mem_raw \<Rightarrow> nat set\<close> where
  \<open>mem_alloc_pool_raw m \<equiv> { x. \<exists>n. memory_allocator_raw m = Some n \<and> x \<ge> n}\<close>

private definition disjoint_mem_raw :: \<open>'v mem_raw \<Rightarrow> 'v mem_raw \<Rightarrow> bool\<close> where
  \<open>disjoint_mem_raw m1 m2 \<longleftrightarrow>
    mem_alloc_pool_raw m1 \<sharp> sh_dom (memory_map_raw m2) \<and>
    sh_dom (memory_map_raw m1) \<sharp> mem_alloc_pool_raw m2 \<and>
    memory_rbt_raw m1 \<sharp> memory_rbt_raw m2 \<and>
    memory_allocator_raw m1 \<sharp> memory_allocator_raw m2\<close>

private definition add_mem_raw :: \<open>'v mem_raw \<Rightarrow> 'v mem_raw \<Rightarrow> 'v mem_raw\<close> where
  \<open>add_mem_raw m1 m2 \<equiv> make_mem_raw (memory_rbt_raw m1 + memory_rbt_raw m2)
     (memory_allocator_raw m1 + memory_allocator_raw m2)\<close>

private lemma add_mem_raw_components:
  shows \<open>memory_allocator_raw (add_mem_raw m1 m2) = memory_allocator_raw m1 + memory_allocator_raw m2\<close>
   and \<open>memory_rbt_raw (add_mem_raw m1 m2) = memory_rbt_raw m1 + memory_rbt_raw m2\<close>
by (auto simp add: add_mem_raw_def)

private lemma add_mem_raw_dom:
  shows \<open>memory_map_raw (add_mem_raw m1 m2) = memory_map_raw m1 + memory_map_raw m2\<close>
by (clarsimp simp add: add_mem_raw_components)

lemma add_mem_raw_comm:
  assumes \<open>disjoint_mem_raw m1 m2\<close>
    shows \<open>add_mem_raw m1 m2 = add_mem_raw m2 m1\<close>
by (metis add_mem_raw_def assms disjoint_mem_raw_def sepalg_comm)

lemma add_mem_raw_preserves_valid_if_disjoint_core:
  assumes \<open>disjoint_mem_raw m1 m2\<close>
      and \<open>mem_is_valid m1\<close>
      and \<open>mem_is_valid m2\<close>
      and \<open>memory_allocator_raw m1 = Some n\<close>
    shows \<open>mem_is_valid (add_mem_raw m1 m2)\<close>
  unfolding mem_is_valid_def add_mem_raw_dom plus_fun_def
proof (intro strip)
  fix n a sh v
  assume n: \<open>memory_allocator_raw (add_mem_raw m1 m2) = Some n\<close>
    and sh: \<open>rbt_share_map_\<alpha>' a (memory_rbt_raw m1) + rbt_share_map_\<alpha>' a (memory_rbt_raw m2) = Shared_Value sh v\<close>
  with assms have [simp]: \<open>memory_allocator_raw m2 = None\<close>
    by (auto simp: disjoint_option_def disjoint_mem_raw_def split!: option.splits)
  have *: \<open>memory_allocator_raw (add_mem_raw m1 m2) = memory_allocator_raw m1\<close>
    using assms by (simp add: add_mem_raw_components plus_option_def)
  show \<open>a < n\<close>
  proof (cases \<open>memory_map_raw m1 a\<close>)
    case Shared_Value
    with n assms show ?thesis
      by (metis add_mem_raw_components(1) mem_is_validE option.case(2) plus_option_def)
  next
    case No_Value
    then have \<open>memory_map_raw m2 a = Shared_Value sh v\<close>
      using sh by auto
    moreover obtain \<open>{x. n \<le> x} \<sharp> {a. \<exists>sh v. rbt_share_map_\<alpha>' a (memory_rbt_raw m2) = Shared_Value sh v}\<close>
     \<open>memory_rbt_raw m1 \<sharp> memory_rbt_raw m2\<close>
      using \<open>disjoint_mem_raw m1 m2\<close> n *
      by (auto simp add: sh_dom_def disjoint_mem_raw_def mem_alloc_pool_raw_def )
    ultimately show ?thesis
      by (metis (mono_tags, lifting) disjoint_iff disjoint_set_def linorder_not_le mem_Collect_eq)
  qed
qed

lemma add_mem_raw_preserves_valid_if_disjoint:
  assumes \<open>disjoint_mem_raw m1 m2\<close>
     and \<open>mem_is_valid m1\<close>
     and \<open>mem_is_valid m2\<close>
   shows \<open>mem_is_valid (add_mem_raw m1 m2)\<close>
proof (cases \<open>memory_allocator_raw m1 = None \<and> memory_allocator_raw m2 = None\<close>)
  case True
  with assms show ?thesis
    by (simp add: add_mem_raw_def mem_is_valid_def plus_option_def)
next
  case False
  then obtain n where \<open>memory_allocator_raw m1 = Some n \<or> memory_allocator_raw m2 = Some n\<close>
    by auto
  then show ?thesis
    by (metis add_mem_raw_comm add_mem_raw_preserves_valid_if_disjoint_core assms disjoint_mem_raw_def disjoint_sym)
qed

private lift_definition disjoint_mem_alt :: \<open>'v mem \<Rightarrow> 'v mem \<Rightarrow> bool\<close> is
  \<open>\<lambda>m1 m2. disjoint_mem_raw m1 m2\<close> .

private lemma disjoint_mem_alt_equiv:
  shows \<open>m1 \<sharp> m2 \<longleftrightarrow> disjoint_mem_alt m1 m2\<close>
by (simp add: disjoint_mem_alt.rep_eq disjoint_mem_def disjoint_mem_raw_def mem_alloc_pool_def
  mem_alloc_pool_raw_def memory_allocator.rep_eq memory_rbt.rep_eq)

lift_definition add_mem :: \<open>'v mem \<Rightarrow> 'v mem \<Rightarrow> 'v mem\<close> is
  \<open>\<lambda>m1 m2. if disjoint_mem_raw m1 m2 then add_mem_raw m1 m2 else m1\<close>
by (simp add: add_mem_raw_preserves_valid_if_disjoint)

lemma add_mem_components:
  assumes \<open>m1 \<sharp> m2\<close>
    shows \<open>memory_allocator (add_mem m1 m2) = memory_allocator m1 + memory_allocator m2\<close>
      and \<open>memory_rbt (add_mem m1 m2) = memory_rbt m1 + memory_rbt m2\<close>
using assms[simplified disjoint_mem_alt_equiv] by (transfer, simp add: add_mem_raw_components)+

lemma add_mem_comm:
  assumes \<open>m1 \<sharp> m2\<close>
    shows \<open>add_mem m1 m2 = add_mem m2 m1\<close>
using assms[simplified disjoint_mem_alt_equiv] by transfer (simp add: add_mem_raw_comm disjoint_mem_raw_def)

end

lemma add_mem_alloc_pool:
    fixes ma me :: \<open>'v mem\<close>
  assumes \<open>ma \<sharp> mb\<close>
    shows \<open>mem_alloc_pool (add_mem ma mb) = mem_alloc_pool ma \<union> mem_alloc_pool mb\<close>
using assms by (auto simp add: mem_alloc_pool_def add_mem_components[OF \<open>ma \<sharp> mb\<close>] plus_option_def
  disjoint_mem_def disjoint_option_def split!: option.splits)

instantiation mem :: (type)strong_sepalg
begin

text\<open>Defining the addition is a bit cumbersome because we need to preserve well-formedness
\<^emph>\<open>unconditionally\<close>, even though we only ever use addition on disjoint inputs.\<close>
definition plus_mem :: \<open>'v mem \<Rightarrow> 'v mem \<Rightarrow> 'v mem\<close> where
  \<open>plus_mem m1 m2 \<equiv> add_mem m1 m2\<close>

lemma plus_mem_components:
    fixes ma me :: \<open>'v mem\<close>
  assumes \<open>ma \<sharp> mb\<close>
    shows \<open>memory_allocator (ma + mb) = memory_allocator ma + memory_allocator mb\<close>
      and \<open>memory_rbt (ma + mb) = memory_rbt ma + memory_rbt mb\<close>
      and \<open>mem_alloc_pool (ma + mb) = mem_alloc_pool ma \<union> mem_alloc_pool mb\<close>
by (simp add: add_mem_components add_mem_alloc_pool assms plus_mem_def)+

lemma plus_add_disj:
    fixes x y z :: \<open>'v mem\<close>
  assumes \<open>x \<sharp> y\<close>
      and \<open>y \<sharp> z\<close>
      and \<open>x \<sharp> z\<close>
    shows \<open>x + y \<sharp> z\<close>
using assms by (auto simp add: disjoint_mem_def disjoint_set_def disjoint_rbt_share_map_def
  plus_mem_components)

lemma plus_add_disj_rev:
    fixes x y z :: \<open>'v mem\<close>
  assumes \<open>x \<sharp> y\<close>
      and \<open>(x + y) \<sharp> z\<close>
    shows \<open>x \<sharp> z\<close>
      and \<open>y \<sharp> z\<close>
using assms  by (auto simp add: disjoint_mem_def disjoint_set_def disjoint_rbt_share_map_def
  plus_mem_components)

instance
proof
   fix x :: \<open>'a mem\<close>
  show \<open>x + 0 = x\<close>
    by (auto simp add: plus_mem_components zero_mem_components
      plus_option_def split!: option.splits intro!: mem_eqI)
next
     fix x y :: \<open>'a mem\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (clarsimp simp add: plus_mem_def add_mem_comm)
next
     fix x y z :: \<open>'a mem\<close>
  assume \<sharp>: \<open>x \<sharp> y\<close> \<open>y \<sharp> z\<close> \<open>x \<sharp> z\<close>
  then have \<open>x + y \<sharp> z\<close> \<open>x \<sharp> (y + z)\<close>
    by (meson \<open>x \<sharp> y\<close> \<open>x \<sharp> z\<close> \<open>y \<sharp> z\<close> disjoint_sym plus_add_disj)+
  with \<sharp> show \<open>x + (y + z) = x + y + z\<close>
      by (intro mem_eqI; smt (verit, best) disjoint_mem_def plus_mem_components sepalg_assoc)
next
     fix x y z :: \<open>'a mem\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x \<sharp> y\<close>
    by (meson disjoint_sym plus_add_disj_rev(1))
next
     fix x y z :: \<open>'a mem\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  then obtain \<open>x \<sharp> z\<close> and \<open>x \<sharp> y\<close>
    by (metis disjoint_sym plus_add_disj_rev)
  then show \<open>x + y \<sharp> z\<close>
    using \<open>y \<sharp> z\<close> plus_add_disj by blast
next
     fix x y z :: \<open>'a mem\<close>
  assume \<open>x \<sharp> y\<close>
    show \<open>x + y \<sharp> z = (y \<sharp> z \<and> x \<sharp> z)\<close>
    by (meson \<open>x \<sharp> y\<close> plus_add_disj plus_add_disj_rev(1) plus_add_disj_rev(2))
qed

end

instantiation mem :: (type)cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>'a mem\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  with plus_mem_components show \<open>x = y\<close>
    by (metis disjoint_mem_def mem_eqI sepalg_cancel_iff)
qed

end

lift_definition (code_dt) write_mem :: \<open>'v mem \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v mem option\<close> is
  \<open>\<lambda>m a v.
     case memory_map_raw m a of
       No_Value \<Rightarrow> None
     | Shared_Value sh _ \<Rightarrow>
        if sh = top then
          Some (m\<lparr> memory_rbt_raw := rbt_share_map_update a (Shared_Value sh v)
                                    (memory_rbt_raw m) \<rparr>)
        else
          None\<close>
    by (auto simp: mem_is_valid_def split: shareable_value.splits)

lemma write_mem_fail0:
  assumes \<open>memory_map m a = No_Value\<close>
    shows \<open>write_mem m a v = None\<close>
using assms by transfer simp

text\<open>For some reason, \<^verbatim>\<open>transfer\<close> does not like \<^verbatim>\<open>top\<close>...\<close>
definition not_top :: \<open>nonempty_share \<Rightarrow> bool\<close> where
  \<open>not_top sh \<equiv> sh \<noteq> top\<close>

lemma write_mem_fail1:
  assumes \<open>memory_map m a = Shared_Value sh v0\<close>
      and \<open>sh \<noteq> top\<close>
    shows \<open>write_mem m a v = None\<close> thm not_top_def[symmetric]
using \<open>sh \<noteq> top\<close>[folded not_top_def] \<open>memory_map m a = Shared_Value sh v0\<close>
  by transfer (clarsimp simp add: not_top_def)

lemma write_mem_success_core:
  assumes \<open>memory_map m a = Shared_Value sh v0\<close>
     and \<open>\<not>not_top sh\<close>
   shows \<open>\<exists>m'. write_mem m a v = Some m' \<and> memory_allocator m' = memory_allocator m \<and>
             memory_rbt m' = rbt_share_map_update a (Shared_Value sh v) (memory_rbt m)\<close>
using assms by transfer (auto simp add: not_top_def mem_is_valid_def)

lemma write_mem_success:
  assumes \<open>memory_map m a = Shared_Value sh vold\<close>
      and \<open>sh = top\<close>
  obtains m' where \<open>write_mem m a v = Some m'\<close> and \<open>memory_allocator m' = memory_allocator m\<close> and
    \<open>memory_rbt m' = rbt_share_map_update a (Shared_Value sh v) (memory_rbt m)\<close>
by (metis assms not_top_def write_mem_success_core)

lemma write_mem_successI:
  assumes \<open>memory_map m a = Shared_Value top v0\<close>
      and \<open>memory_allocator m' = memory_allocator m\<close>
      and \<open>memory_rbt m' = rbt_share_map_update a (Shared_Value top v) (memory_rbt m)\<close>
    shows \<open>write_mem m a v = Some m'\<close>
  by (metis assms mem_eqI write_mem_success)

lemma write_mem_success_reverse:
  assumes \<open>write_mem m a v = Some m'\<close>
  obtains v0 where \<open>memory_map m a = Shared_Value top v0\<close>
using assms by (metis option.simps(3) shareable_value.exhaust write_mem_fail0 write_mem_fail1)

lemma write_mem_success_reverse'':
  assumes \<open>write_mem m a v = Some m'\<close>
  obtains v0 where \<open>memory_map m a = Shared_Value top v0\<close> and \<open>memory_allocator m' = memory_allocator m\<close> and
    \<open>memory_rbt m' = rbt_share_map_update a (Shared_Value top v) (memory_rbt m)\<close>
  by (metis assms option.inject write_mem_success write_mem_success_reverse)

lemma write_mem_success_reverse':
  assumes \<open>write_mem m a v = Some m'\<close>
    shows \<open>memory_allocator m' = memory_allocator m\<close>
      and \<open>memory_rbt m' = rbt_share_map_update a (Shared_Value top v) (memory_rbt m)\<close>
by (meson assms write_mem_success_reverse'')+

lemma write_mem_success_reverse'E:
  assumes \<open>write_mem m a v = Some m'\<close>
      and \<open>\<And>v0. memory_allocator m' = memory_allocator m \<Longrightarrow> memory_map m a = Shared_Value top v0 \<Longrightarrow>
            memory_rbt m' = rbt_share_map_update a (Shared_Value top v) (memory_rbt m) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (meson write_mem_success_reverse'')

lemma write_mem_success_perm_map:
  shows \<open>mem_perm_map s a = top \<longleftrightarrow> (\<exists>s'. write_mem s a v = Some s')\<close> (is \<open>?L = ?R\<close>)
proof 
  assume ?L
  with shares_nontrivial have \<open>\<exists>v0. memory_map s a = Shared_Value top v0\<close>
    by (auto simp add: mem_perm_map_def shareable_value_to_share_def nonempty_share_top_eq 
        split!: shareable_value.splits simp del: shares_nontrivial)
  then show ?R
    by (meson write_mem_success)
next
  assume ?R
  then obtain s' v0 where \<open>write_mem s a v = Some s'\<close> \<open>memory_map s a = Shared_Value top v0\<close>
    by (meson write_mem_success_reverse)
  then show ?L
    by (simp add: mem_perm_map_def nonempty_share_top_eq shareable_value_to_share_def)
qed

text\<open>Note that the \<^verbatim>\<open>zero\<close> instance here is being used merely as a way of obtaining a ``default''
value when inserting the newly-allocated reference into the domain of the memory.  The value being
inserted is not actually important, just the fact that \<^emph>\<open>something\<close> is there.  We previously used
\<^verbatim>\<open>undefined\<close> here but OCaml evaluates this eagerly causing spurious runtime failures during
conformance testing.\<close>
lift_definition (code_dt) alloc_mem :: \<open>'v::{default} mem \<Rightarrow> (nat \<times> 'v mem) option\<close> is
  \<open>\<lambda>m.
    case memory_allocator_raw m of
      None   \<Rightarrow> None
    | Some a \<Rightarrow>
        Some (a, m\<lparr> memory_allocator_raw := Some (a + 1),
                    memory_rbt_raw := rbt_share_map_update a (Shared_Value top default)
                                    (memory_rbt_raw m) \<rparr>)\<close>
  by (auto simp: less_Suc_eq mem_is_valid_def split: option.splits)

lemma alloc_mem_fail:
  assumes \<open>memory_allocator m = None\<close>
    shows \<open>alloc_mem m = None\<close>
using assms by transfer simp

lemma alloc_mem_success_core:
  assumes \<open>memory_allocator m = Some n\<close>
    shows \<open>\<exists>m'. alloc_mem m = Some (n, m') \<and> memory_allocator m' = Some (n+1) \<and>
              memory_rbt m' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m)\<close>
proof -
  have \<open>mem_is_valid (Rep_mem m)\<close>
    using Rep_mem by auto
  from this assms show ?thesis
    by (clarsimp simp add: memory_allocator_def alloc_mem_def Abs_mem_inverse less_SucI
      mem_is_valid_def memory_rbt.rep_eq)
qed

lemma alloc_mem_success:
  assumes \<open>memory_allocator m = Some n\<close>
  obtains m' where \<open>alloc_mem m = Some (n, m')\<close> and \<open>memory_allocator m' = Some (n+1)\<close> and
      \<open>memory_rbt m' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m)\<close>
by (meson alloc_mem_success_core assms)

lemma alloc_mem_successI:
  assumes \<open>memory_allocator m = Some n\<close>
      and \<open>memory_allocator m' = Some (n+1)\<close>
      and \<open>memory_rbt m' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m)\<close>
    shows \<open>alloc_mem m = Some (n, m')\<close>
by (metis alloc_mem_success assms mem_eqI)

lemma alloc_mem_success_reverse:
  assumes \<open>alloc_mem m = Some (n,m')\<close>
    shows \<open>memory_allocator m = Some n\<close>
      and \<open>memory_allocator m' = Some (n+1)\<close>
      and \<open>memory_rbt m' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m)\<close>
by (metis alloc_mem_fail alloc_mem_success_core assms not_Some_eq option.sel prod.inject)+

lemma alloc_mem_success_reverseE:
  assumes \<open>alloc_mem m = Some (n,m')\<close>
      and \<open>memory_allocator m = Some n \<Longrightarrow> memory_allocator m' = Some (n+1) \<Longrightarrow>
            memory_rbt m' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m) \<Longrightarrow> R\<close>
    shows R
using alloc_mem_success_reverse assms by blast

lemma alloc_mem_success_reverse':
  assumes \<open>alloc_mem m = Some (n, m')\<close>
    shows \<open>n \<in> mem_alloc_pool m\<close>
      and \<open>mem_alloc_pool m' = mem_alloc_pool m - {n}\<close>
      and \<open>n \<notin> dom_mem m\<close>
      and \<open>dom_mem m' = dom_mem m \<union> {n}\<close>
      and \<open>\<And>a. memory_map m' a = (if a = n then Shared_Value top default else memory_map m a)\<close>
proof -
  from assms obtain n' where n': \<open>memory_allocator m = Some n'\<close>
    by (metis alloc_mem_fail option.exhaust_sel option.simps(3))
  from this assms and alloc_mem_success obtain m'' where \<open>alloc_mem m = Some (n, m'')\<close> and
      \<open>memory_allocator m'' = Some (n+1)\<close> and
      \<open>memory_rbt m'' = rbt_share_map_update n (Shared_Value top default) (memory_rbt m)\<close>
    by fastforce
  moreover from this and assms have [simp]: \<open>n' = n\<close> \<open>m'' = m'\<close>
    using \<open>memory_allocator m = Some n'\<close> alloc_mem_success_core by force+
  then show \<open>n \<in> mem_alloc_pool m\<close>
    using n' assms by (simp add: mem_alloc_pool_def)
  moreover 
  show \<open>mem_alloc_pool m' = mem_alloc_pool m - {n}\<close>
    using assms n' calculation by (auto simp add: mem_alloc_pool_def)   
  show \<open>n \<notin> dom_mem m\<close>
    using mem_alloc_pool_dom_disjoint calculation by blast
  from calculation show \<open>dom_mem m' = dom_mem m \<union> {n}\<close>
    by (auto simp add: dom_mem_def sh_dom_def)
  ultimately show \<open>\<And>a. memory_map m' a = (if a = n then Shared_Value top default else memory_map m a)\<close>
    by auto
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma alloc_mem_success_reverseE':
  assumes \<open>alloc_mem m = Some (n,m')\<close>
      and \<open>memory_allocator m = Some n \<Longrightarrow> n \<in> mem_alloc_pool m \<Longrightarrow> mem_alloc_pool m' = mem_alloc_pool m - {n} \<Longrightarrow>
            n \<notin> dom_mem m \<Longrightarrow> dom_mem m' = dom_mem m \<union> {n} \<Longrightarrow> R\<close>
    shows R
by (meson alloc_mem_success_reverse' alloc_mem_success_reverse assms)

definition read_mem :: \<open>'v mem \<Rightarrow> nat \<Rightarrow> 'v option\<close> where
  \<open>read_mem m a \<equiv>
     case memory_map m a of
       No_Value         \<Rightarrow> None
     | Shared_Value _ v \<Rightarrow> Some v\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma read_mem_zero:
  shows \<open>read_mem 0 k = None\<close>
by (clarsimp simp add: read_mem_def zero_mem_components zero_fun_def)

lemma read_mem_write_mem_commute:
  assumes \<open>write_mem m k v = Some m'\<close>
    shows \<open>read_mem m' k = Some v\<close>
proof -
  from assms obtain v0 where \<open>memory_map m k = Shared_Value top v0\<close>
    by (meson write_mem_success_reverse)
  from this and write_mem_success have \<open>memory_map m' k = Shared_Value top v\<close>
    by (metis assms fun_upd_apply option.inject rbt_share_map_\<alpha>_update)
  from this show ?thesis
    unfolding read_mem_def by simp
qed

lemma write_mem_self_commute:
  assumes \<open>k \<noteq> k'\<close>
      and \<open>write_mem m k v = Some m1\<close>
      and \<open>write_mem m k' v' = Some m2\<close>
    shows \<open>write_mem m1 k' v' = write_mem m2 k v\<close>
proof -
  from assms obtain v0 v0' where \<open>memory_map m k = Shared_Value top v0\<close> and
      \<open>memory_map m k' = Shared_Value top v0'\<close>
    by (meson write_mem_success_reverse)
  with assms have \<open>memory_map m2 k = Shared_Value top v0\<close> and
      \<open>memory_map m1 k' = Shared_Value top v0'\<close>
    by (metis fun_upd_apply option.inject rbt_share_map_\<alpha>_update write_mem_success)+
  then obtain m1' and m2' where \<open>write_mem m1 k' v' = Some m1'\<close> \<open>write_mem m2 k v = Some m2'\<close>
    by (meson write_mem_success)
  then have \<open>m1' = m2'\<close>
    using assms by (intro mem_eqI; clarsimp elim!: write_mem_success_reverse'E simp add:
      fun_upd_twist rbt_share_map_eqI)
  with \<open>write_mem m1 k' v' = Some m1'\<close> and \<open>write_mem m2 k v = Some m2'\<close> show ?thesis
    by simp
qed

lemma write_mem_self_commute_one:
  fixes m1 :: \<open>'v mem\<close>
  assumes \<section>: \<open>write_mem m k v = Some m1\<close>
       and \<open>write_mem m k' v' = None\<close>
    shows \<open>Option.bind (write_mem m k v) (\<lambda>\<sigma>'. write_mem \<sigma>' k' v') =
              Option.bind (write_mem m k' v') (\<lambda>\<sigma>'. write_mem \<sigma>' k v)\<close>
proof -
  have \<open>write_mem m1 k' v' = None\<close>
    using assms write_mem_success_reverse'E[OF \<section>]
    by (metis fun_upd_apply mem_perm_map_def not_None_eq rbt_share_map_\<alpha>_update write_mem_success_perm_map)
  with assms show ?thesis by auto
qed

lemma write_mem_self_commute':
    fixes m :: \<open>'v mem\<close>
  assumes \<open>k \<noteq> k'\<close>
    shows \<open>Option.bind (write_mem m k v) (\<lambda>\<sigma>'. write_mem \<sigma>' k' v') =
              Option.bind (write_mem m k' v') (\<lambda>\<sigma>'. write_mem \<sigma>' k v)\<close>
  by (metis (no_types, lifting) assms bind.bind_lunit bind.bind_lzero option.collapse write_mem_self_commute write_mem_self_commute_one)

lemma write_mem_collapse:
  assumes \<open>write_mem m k v = Some m'\<close>
    shows \<open>write_mem m' k v' = write_mem m k v'\<close>
proof -
  from assms obtain m'' where \<open>write_mem m' k v' = Some m''\<close>
    by (elim write_mem_success_reverse'E) (metis fun_upd_same rbt_share_map_\<alpha>_update write_mem_success)
  moreover from assms obtain m''' where \<open>write_mem m k v' = Some m'''\<close>
    by (meson write_mem_success write_mem_success_reverse)
  ultimately have \<open>m'' = m'''\<close>
    using assms by (auto simp add: write_mem_success_reverse' rbt_share_map_eqI intro!: mem_eqI)
  from this and \<open>write_mem m' k v' = Some m''\<close> and \<open>write_mem m k v' = Some m'''\<close> show ?thesis
    by simp
qed

lemma alloc_mem_preserves_valid:
  assumes \<open>mem_can_alloc m\<close>
      and \<open>alloc_mem m = Some (a,m')\<close>
    shows \<open>mem_can_alloc m'\<close>
  by (meson alloc_mem_success_reverseE assms(2) mem_can_alloc_def)


\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma write_mem_preserves_valid:
  assumes \<open>mem_can_alloc m\<close>
      and \<open>write_mem m a v = Some m'\<close>
      and \<open>a \<in> dom_mem m\<close>
    shows \<open>mem_can_alloc m'\<close>
using assms by (clarsimp simp add: mem_can_alloc_def elim!: write_mem_success_reverse'E)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma plus_mem_preserves_valid:
  assumes \<open>mem_can_alloc m1\<close>
      and \<open>m1 \<sharp> m2\<close>
    shows \<open>mem_can_alloc (m1 + m2)\<close>
using assms by (clarsimp simp add: mem_can_alloc_def plus_mem_components plus_option_def)

lemma read_mem_local_action:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>read_mem m1 a = Some v\<close>
    shows \<open>read_mem (m1 + m2) a = Some v\<close>
using assms plus_shareable_value.elims by (auto simp add: read_mem_def disjoint_mem_def
  plus_mem_components plus_fun_def split!: shareable_value.splits)

lemma Shared_Value_plus_neq_No_Value [simp]:
  shows \<open>Shared_Value sh v + s \<noteq> No_Value\<close>
by (cases s) auto

lemma Shared_Value_Top_Disj:
  assumes \<open>Shared_Value top v \<sharp> sh\<close>
    shows \<open>sh = No_Value\<close>
  by (meson assms shareable_value_disjoint_top(1))

lemma None_disjoint_memory_allocator [simp]: 
  shows \<open>None \<sharp> memory_allocator (m::'a mem)\<close> \<open>memory_allocator (m::'a mem) \<sharp> None\<close>
  by (metis zero_disjoint zero_disjoint2 zero_option_def)+

lemma write_mem_local_action2:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>write_mem m1 a v = Some m1'\<close>
    shows \<open>m1' \<sharp> m2\<close>
proof -
  from assms obtain v0 where \<open>memory_map m1 a = Shared_Value top v0\<close>
    by (meson write_mem_success_reverse)
  moreover from this and \<open>m1 \<sharp> m2\<close> have \<open>memory_map m2 a = No_Value\<close>
    by (metis Shared_Value_Top_Disj disjoint_fun_def disjoint_mem_def disjoint_rbt_share_map_def)
  moreover from calculation \<open>m1 \<sharp> m2\<close> and \<open>write_mem m1 a v = Some m1'\<close> show \<open>m1' \<sharp> m2\<close>
    by (elim write_mem_success_reverse'E) (auto simp add: disjoint_mem_def mem_alloc_pool_def
      disjoint_set_def disjoint_iff sh_dom_def disjoint_fun_def  disjoint_rbt_share_map_def)
qed

lemma write_mem_local_action1:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>write_mem m1 a v = Some m1'\<close>
    shows \<open>write_mem (m1 + m2) a v = Some (m1' + m2)\<close>
proof -
  from assms have \<open>m1' \<sharp> m2\<close>
    by (meson write_mem_local_action2)
  moreover from assms obtain v0 where \<open>memory_map m1 a = Shared_Value top v0\<close>
    by (meson write_mem_success_reverse)
  with\<open>m1 \<sharp> m2\<close> have \<open>memory_map m2 a = No_Value\<close>
    by (metis Shared_Value_Top_Disj disjoint_fun_def disjoint_mem_def disjoint_rbt_share_map_def)
  ultimately show ?thesis
    using assms by (auto simp add: disjoint_mem_def plus_mem_components plus_fun_def disjoint_fun_def
      disjoint_rbt_share_map_def elim!: write_mem_success_reverse'E intro!: write_mem_successI
      rbt_share_map_eqI)
qed

lemma write_mem_local_action:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>write_mem m1 a v = Some m1'\<close>
    shows \<open>write_mem (m1 + m2) a v = Some (m1' + m2) \<and> m1' \<sharp> m2\<close>
using assms by (metis write_mem_local_action1 write_mem_local_action2)

lemma alloc_mem_local_action2:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>alloc_mem m1 = Some (a, m1')\<close>
    shows \<open>m1' \<sharp> m2\<close>
proof -
  have \<open>\<lbrakk> \<forall>x\<ge>a. \<forall>sh v. rbt_share_map_\<alpha>' x (memory_rbt m2) \<noteq> Shared_Value sh v\<rbrakk>
    \<Longrightarrow> Shared_Value \<top> default \<sharp> rbt_share_map_\<alpha>' a (memory_rbt m2)\<close>
    using disjoint_shareable_value.elims(3) by force
  then show ?thesis
    using assms 
    by (force elim!: alloc_mem_success_reverseE simp add: disjoint_mem_def
        disjoint_iff mem_alloc_pool_def disjoint_fun_def disjoint_option_def  disjoint_set_def
        disjoint_rbt_share_map_def split!: option.splits)
qed

lemma alloc_mem_local_action1:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>alloc_mem m1 = Some (a, m1')\<close>
    shows \<open>alloc_mem (m1 + m2) = Some (a, m1' + m2)\<close>
proof -
  from assms have \<open>m1' \<sharp> m2\<close>
    using alloc_mem_local_action2 by blast
  with \<open>m1 \<sharp> m2\<close> have \<open>memory_map m2 a = No_Value\<close>
    by (metis Shared_Value_Top_Disj alloc_mem_success_reverse'(5) assms(2) disjoint_fun_def disjoint_mem_def disjoint_rbt_share_map_def)
  then show ?thesis
    using assms by (auto elim!: alloc_mem_success_reverseE intro!: alloc_mem_successI
      rbt_share_map_eqI simp add: disjoint_fun_def disjoint_rbt_share_map_def plus_fun_def
      disjoint_rbt_share_map_def disjoint_mem_def plus_mem_components[OF \<open>m1 \<sharp> m2\<close>]
      plus_mem_components[OF \<open>m1' \<sharp> m2\<close>] disjoint_option_def plus_option_def split!: option.splits)
qed

lemma alloc_mem_local_action:
  assumes \<open>m1 \<sharp> m2\<close>
      and \<open>alloc_mem m1 = Some (a, m1')\<close>
    shows \<open>alloc_mem (m1 + m2) = Some (a, m1' + m2) \<and> m1' \<sharp> m2\<close>
using assms by (metis alloc_mem_local_action1 alloc_mem_local_action2)

lemma restrict_shareable_map_perms':
  fixes m :: \<open>'v mem\<close>
    and p :: \<open>nat \<Rightarrow> share\<close>
  shows \<open>shareable_value_to_share ((restrict_shareable_map (memory_map m) p) k) = inf (mem_perm_map m k) (p k)\<close>
by (clarsimp simp add: mem_perm_map_def restrict_shareable_map_def)  (metis (no_types)
  restrict_shareable_map_def restrict_shareable_map_perms)

lemma sh_dom_restrict:
  shows \<open>sh_dom (restrict_shareable_map (memory_map m) p) = { a. inf (mem_perm_map m a) (p a) \<noteq> bot }\<close>
  by (auto simp add: sh_dom_def restrict_shareable_map_def to_nonempty_share_def mem_perm_map_def
  restrict_nonempty_share_def shareable_value_to_share_def split: shareable_value.splits)

lemma sh_dom_restrict_sub:
  shows \<open>sh_dom (restrict_shareable_map (memory_map m) p) \<subseteq> sh_dom (memory_map m)\<close>
  unfolding sh_dom_restrict
  by (force simp add: sh_dom_def mem_perm_map_def shareable_value_to_share_def
    split!: shareable_value.splits)

lemma restrict_shareable_map_join:
  assumes \<open>\<And>a. (p1 + p2) a = (case m a of No_Value \<Rightarrow> bot | Shared_Value sh _ \<Rightarrow> Rep_nonempty_share sh)\<close>
  shows \<open>m = restrict_shareable_map m p1 + restrict_shareable_map m p2\<close>
proof (clarsimp simp: restrict_shareable_map_def plus_fun_def split: shareable_value.splits intro !: ext)
  fix x sh v
  assume x: \<open>m x = Shared_Value sh v\<close>
  then obtain \<open>p1 x \<le> Rep_nonempty_share sh\<close> \<open>p2 x \<le> Rep_nonempty_share sh\<close>
    by (metis assms plus_fun_def plus_share_def shareable_value.simps(4) sup_ge1 sup_ge2)
  with x assms [of x] Rep_nonempty_share [of sh] 
  show \<open>Shared_Value sh v = (case restrict_nonempty_share (p1 x) sh of None \<Rightarrow> No_Value | Some sh' \<Rightarrow> Shared_Value sh' v)
                          + (case restrict_nonempty_share (p2 x) sh of None \<Rightarrow> No_Value | Some sh' \<Rightarrow> Shared_Value sh' v)\<close>
    apply (simp add: plus_share_def to_nonempty_share_def restrict_nonempty_share_def plus_fun_def)
    by (metis Rep_nonempty_share_inverse bot.not_eq_extremum eq_onp_same_args inf.absorb2 plus_nonempty_share.abs_eq sup_bot_left
        sup_bot_right)
qed

lift_definition mem_drop_allocator :: \<open>'v mem \<Rightarrow> 'v mem\<close> is
  \<open>\<lambda>m. m\<lparr> memory_allocator_raw := None \<rparr>\<close>
by (clarsimp simp add: mem_is_valid_def)

lemma mem_drop_allocator_components [simp]:
  shows \<open>memory_allocator (mem_drop_allocator m) = None\<close>
    and \<open>memory_rbt (mem_drop_allocator m) = memory_rbt m\<close>
by (transfer, simp)+

lemma mem_drop_allocator_mem_pool [simp]:
  shows \<open>mem_alloc_pool (mem_drop_allocator m) = {}\<close>
by (clarsimp simp add: mem_alloc_pool_def mem_drop_allocator_components)

lemma mem_drop_allocator_perm_map [simp]:
  shows \<open>mem_perm_map (mem_drop_allocator m) = mem_perm_map m\<close>
by (clarsimp simp add: mem_perm_map_def mem_drop_allocator_components intro!: ext)

lift_definition mem_drop_allocations :: \<open>'v mem \<Rightarrow> 'v mem\<close> is
  \<open>\<lambda>m. m\<lparr> memory_rbt_raw := 0 \<rparr>\<close>
by (clarsimp simp add: mem_is_valid_def zero_fun_def)

lemma mem_drop_allocations_components [simp]:
  shows \<open>memory_allocator (mem_drop_allocations m) = memory_allocator m\<close>
    and \<open>memory_rbt (mem_drop_allocations m) = 0\<close>
by (transfer, simp)+

lemma mem_drop_allocations_perm_map [simp]:
  shows \<open>mem_perm_map (mem_drop_allocations m) = 0\<close>
by (clarsimp simp add: zero_fun_def mem_perm_map_def mem_drop_allocations_components
  shareable_value_to_share_def zero_share_def intro!: ext)

lift_definition mem_restrict_permissions :: \<open>'v mem \<Rightarrow> (nat \<Rightarrow> share) \<Rightarrow> 'v mem\<close> is
  \<open>\<lambda>m p. m \<lparr> memory_rbt_raw := rbt_share_map_restrict p (memory_rbt_raw m) \<rparr>\<close>
by (clarsimp simp add: mem_is_valid_def rbt_share_map_\<alpha>_restrict restrict_shareable_map_def)
  (metis shareable_value.exhaust shareable_value.simps(5))

lemma mem_restrict_permissions_components:
  shows \<open>memory_allocator (mem_restrict_permissions m p) = memory_allocator m\<close>
    and \<open>memory_rbt (mem_restrict_permissions m p) = rbt_share_map_restrict p (memory_rbt m)\<close>
by (transfer, simp)+

lemma mem_restrict_permissions_alloc_pool:
  shows \<open>mem_alloc_pool (mem_restrict_permissions m p) = mem_alloc_pool m\<close>
by (clarsimp simp add: mem_alloc_pool_def mem_restrict_permissions_components)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma mem_restrict_permissions_memory_map:
  shows \<open>memory_map (mem_restrict_permissions m p) = restrict_shareable_map (memory_map m) p\<close>
  by (simp add: mem_restrict_permissions_components(2) rbt_share_map_\<alpha>_restrict)

lemma mem_split_perm:
  assumes \<open>p1 \<sharp> p2\<close>
      and \<open>mem_perm_map m = p1 + p2\<close>
    shows \<open>\<exists>m1 m2. m1 \<sharp> m2 \<and> m = m1 + m2 \<and> mem_perm_map m1 = p1 \<and> mem_perm_map m2 = p2\<close>
proof -
  let ?m1 = \<open>(mem_restrict_permissions (mem_drop_allocator m) p1)\<close>
  let ?m2 = \<open>mem_restrict_permissions m p2\<close>
  have \<open>mem_alloc_pool m \<sharp>
         sh_dom (restrict_shareable_map (rbt_share_map_\<alpha> (memory_rbt m)) p1)\<close>
    by (metis (no_types, lifting) disjoint_iff disjoint_set_def sh_dom_restrict_sub dom_mem_def 
        mem_alloc_pool_dom_disjoint subsetD)
  moreover 
  have \<open>mem_alloc_pool (mem_drop_allocator m) \<sharp>
         sh_dom (restrict_shareable_map (rbt_share_map_\<alpha> (memory_rbt m)) p2)\<close>
    by (simp add: disjoint_set_def mem_drop_allocator_mem_pool)
  moreover
  have \<open>rbt_share_map_restrict p1 (memory_rbt m) \<sharp>
           rbt_share_map_restrict p2 (memory_rbt m)\<close>
    by (simp add: \<open>p1 \<sharp> p2\<close> disjoint_rbt_share_map_def rbt_share_map_\<alpha>_restrict restrict_shareable_map_disjoint)
  ultimately have \<open>?m1 \<sharp> ?m2\<close>
    by (simp add: disjoint_mem_def mem_alloc_pool_def mem_restrict_permissions_components rbt_share_map_\<alpha>_restrict)
  then have \<open>?m2 \<sharp> ?m1\<close>
    by fastforce
  moreover have \<open>m = ?m1 + ?m2\<close>
  proof (intro mem_eqI rbt_share_map_eqI)
    show \<open>memory_allocator m = memory_allocator (mem_restrict_permissions (mem_drop_allocator m) p1 + mem_restrict_permissions m p2)\<close>
      using \<open>?m1 \<sharp> ?m2\<close> \<open>?m2 \<sharp> ?m1\<close>
      by (metis mem_drop_allocator_components(1) mem_restrict_permissions_components(1) plus_mem_components(1) sepalg_ident zero_option_def)

    show \<open>rbt_share_map_\<alpha> (memory_rbt m) =
          rbt_share_map_\<alpha> (memory_rbt (mem_restrict_permissions (mem_drop_allocator m) p1 + mem_restrict_permissions m p2))\<close>
      using assms
      apply (simp add: plus_mem_components[OF \<open>?m1 \<sharp> ?m2\<close>] plus_mem_components[OF \<open>?m2 \<sharp> ?m1\<close>] mem_restrict_permissions_components)
      by (metis mem_perm_map_def rbt_share_map_\<alpha>_restrict restrict_shareable_map_join shareable_value_to_share_def)
  qed
  moreover have \<open>mem_perm_map ?m1 = p1\<close> and \<open>mem_perm_map ?m2 = p2\<close>
    by (auto simp add: assms mem_perm_map_def mem_restrict_permissions_components
       inf.absorb1 inf_commute plus_fun_def plus_share_def rbt_share_map_\<alpha>_restrict restrict_shareable_map_perms')
  ultimately show \<open>\<exists>m1 m2. m1 \<sharp> m2 \<and> m = m1 + m2 \<and> mem_perm_map m1 = p1 \<and> mem_perm_map m2 = p2\<close>
    using disjoint_sym by blast
qed

lemma mem_drop_allocations_disjoint:
  shows \<open>mem_drop_allocations m \<sharp> mem_drop_allocator m\<close>
  using mem_alloc_pool_dom_disjoint
  unfolding dom_mem_def mem_alloc_pool_def disjoint_mem_def mem_alloc_pool_def
  by (auto simp add: mem_drop_allocations_components zero_fun_def disjoint_set_def disjoint_option_def)

lemma mem_drop_allocations_split:
  shows \<open>m = mem_drop_allocations m + mem_drop_allocator m\<close>
proof (intro mem_eqI)
  show \<open>memory_allocator m = memory_allocator (mem_drop_allocations m + mem_drop_allocator m)\<close>
    by (simp add: mem_drop_allocations_components(1) mem_drop_allocations_disjoint option.case_eq_if plus_mem_components plus_option_def)
  show \<open>memory_rbt m = memory_rbt (mem_drop_allocations m + mem_drop_allocator m)\<close>
    by (simp add: mem_drop_allocations_components(2) mem_drop_allocations_disjoint plus_mem_components(2))
qed

lemma mem_split_allocator:
  assumes \<open>mem_can_alloc m\<close>
    shows \<open>\<exists>m1 m2. m = m1 + m2 \<and> m1 \<sharp> m2 \<and> mem_alloc_pool m1 = mem_alloc_pool m \<and>
            mem_alloc_pool m2 = {} \<and> mem_can_alloc m1 \<and> (\<forall>a. mem_perm_map m1 a = bot) \<and>
            (\<forall>a. mem_perm_map m2 a = mem_perm_map m a)\<close>
proof (intro exI conjI)
  let ?m2 = \<open>mem_drop_allocator m\<close>
  let ?m1 = \<open>mem_drop_allocations m\<close>
  show \<open>m = ?m1 + ?m2\<close>
    by (simp add: mem_drop_allocations_split)
  show \<open>?m1 \<sharp> ?m2\<close>
    by (simp add: mem_drop_allocations_disjoint)
  show \<open>mem_can_alloc ?m1\<close>                            
    by (metis assms mem_can_alloc_def mem_drop_allocations_components(1))
qed (auto simp: zero_fun_def zero_share_def mem_alloc_pool_def)

lift_definition mem_to_alist :: \<open>'v mem \<Rightarrow> (nat \<times> 'v) list\<close>
  is \<open>\<lambda>m.  List.map (\<lambda> (k, v, _). (k, v)) (rbt_share_map_entries (memory_rbt m))\<close> .

definition dummy_max :: \<open>nat set \<Rightarrow> nat\<close>
  where \<open>dummy_max ls \<equiv> if ls = {} then 0 else Max ls\<close>

lift_definition mem_from_alist :: \<open>(nat \<times> 'v) list \<Rightarrow> 'v mem\<close>
  is \<open>\<lambda>l. make_mem_raw (rbt_share_map_bulkload_top l) 
         (if length l = 0 then Some 0 else 
             Some (1 + Max (fst ` set l)))\<close>
  apply (clarsimp simp add: mem_is_valid_def rbt_share_map_\<alpha>_def rbt_share_map_bulkload_top_def
    rbt_share_map_bulkload_def shareable_value_option_def split: option.splits)
  apply transfer'
  apply (clarsimp simp add: map_of_map)
  apply (metis Max_ge domI dom_map_of_conv_image_fst finite_dom_map_of le_imp_less_Suc)
  done

(*<*)
end
(*>*)