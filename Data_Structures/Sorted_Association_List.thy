(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Sorted_Association_List
  imports "HOL-Library.Product_Lexorder"
begin

section\<open>Sorted association lists\<close>

subsection\<open>Supporting definitions\<close>

definition salist_inv :: \<open>('k::{linorder} \<times> 'v) list \<Rightarrow> bool\<close> where
  \<open>salist_inv s \<longleftrightarrow> distinct (List.map fst s) \<and> sorted (List.map fst s)\<close>

lemma salist_invE:
  assumes \<open>salist_inv s\<close>
    and \<open>distinct (List.map fst s) \<Longrightarrow> sorted (List.map fst s) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
using assms by (auto simp add: salist_inv_def)

lemma salist_Cons_downward_closedD:
  assumes \<open>salist_inv (k#ks)\<close>
  shows \<open>salist_inv ks\<close>
using assms by (auto simp add: salist_inv_def)

lemma salist_lt_ConsI:
  assumes \<open>salist_inv ss\<close>
      and *: \<open>\<And>l. l \<in> fst ` set ss \<Longrightarrow> k < l\<close>
    shows \<open>salist_inv ((k, v)#ss)\<close>
proof -
  from * have \<open>\<And>l. l \<in> fst ` set ss \<Longrightarrow> k \<noteq> l\<close>
    by blast
  from this and assms have \<open>distinct (List.map fst ((k, v)#ss))\<close>
    by (metis distinct.simps(2) fst_eqD image_set list.simps(9) salist_inv_def)
  moreover from this and assms have \<open>sorted (List.map fst ((k, v)#ss))\<close>
    by (metis fst_conv list.set_map list.simps(9) salist_invE strict_sorted_iff strict_sorted_simps(2))
  ultimately show ?thesis
    using salist_inv_def by blast
qed 

lemma salist_invI [intro!]:
  assumes \<open>distinct (List.map fst s)\<close>
      and \<open>sorted (List.map fst s)\<close>
    shows \<open>salist_inv s\<close>
using assms by (auto simp add: salist_inv_def)

fun ainsert :: \<open>('k::{linorder} \<times> 'v) list \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) list\<close> where
  \<open>ainsert []          k v = [(k, v)]\<close> |
  \<open>ainsert ((m, q)#ks) k v =
     (if k = m then
        ((k, v)#ks)
      else if k < m then
        [(k, v), (m, q)]@ks
      else (m, q)#(ainsert ks k v))\<close>

lemmas ainsert_induct = ainsert.induct[case_names ANil ACons]

lemma ainsert_greater [simp]:
  \<open>k > m \<Longrightarrow> ainsert ((m, q)#ks) k v = (m, q)#(ainsert ks k v)\<close>
  by auto

lemma ainsert_key_set_characterisation [simp]:
  shows \<open>fst ` set (ainsert ks k v) \<subseteq> fst ` set ks \<union> { k }\<close>
proof (induct ks k v rule: ainsert_induct)
  case (ANil k v)
  then show ?case by force
next
  case (ACons m q ks k v)
  then show ?case
    by (cases k m rule: linorder_cases) auto
qed

lemma ainsert_distinct_keys:
  assumes \<open>k \<noteq> m\<close> and \<open>m \<notin> fst ` set ks\<close>
  shows \<open>m \<notin> fst ` set (ainsert ks k v)\<close>
using assms by (metis UnE ainsert_key_set_characterisation empty_iff insert_absorb insert_iff insert_subset)

lemma ainsert_salist_inv_preserve:
  fixes ks :: \<open>('a::{linorder} \<times> 'b) list\<close>
  shows \<open>salist_inv ks \<Longrightarrow> salist_inv (ainsert ks k v)\<close>
proof (induct ks k v rule: ainsert_induct)
  case (ANil k v)
  then show ?case
    by force
next
  case (ACons m q ks k v)
  show ?case 
  proof (cases k m rule: linorder_cases)
    case greater
    with ACons ainsert_key_set_characterisation[of ks k v] ainsert_distinct_keys [of k m ks]
    show ?thesis
      by (fastforce simp add: salist_inv_def)
  qed (use ACons in \<open>auto simp: salist_inv_def\<close>)
qed

lemma map_of_ainsert_eq [simp]:
  shows \<open>map_of (ainsert ks k v) k = Some v\<close>
  by (induction ks) auto

lemma map_of_ainsert_neq [simp]:
  shows \<open>\<lbrakk>salist_inv ks; k \<noteq> k'\<rbrakk> \<Longrightarrow> map_of (ainsert ks k v) k' = map_of ks k'\<close>
proof (induct ks k v rule: ainsert_induct)
  case (ANil k v)
  then show ?case by force
next
  case (ACons m q ks k v)
  then show ?case
    by (auto simp: salist_Cons_downward_closedD)
qed

fun adelete :: \<open>('k::{linorder} \<times> 'v) list \<Rightarrow> 'k \<Rightarrow> ('k \<times> 'v) list\<close> where
  \<open>adelete [] k = []\<close> |
  \<open>adelete ((m, q)#ks) k =
    (if m = k then ks else (m, q)#adelete ks k)\<close>

lemmas adelete_induct = adelete.induct[case_names ANil ACons]

lemma adelete_key_set_characterisation [simp]:
  shows \<open>fst ` set ks - { k } \<subseteq> fst ` set (adelete ks k)\<close>
by (induction ks k rule: adelete_induct) auto

lemma adelete_deletes_keys:
  shows \<open>salist_inv ks \<Longrightarrow> k \<notin> fst ` set (adelete ks k)\<close>
proof (induct ks k rule: adelete_induct)
  case (ANil k)
  then show ?case
    by simp
next
  case (ACons m q ks k)
  then show ?case
    by (auto simp: salist_inv_def image_iff dest: split: prod.splits)
qed

lemma adelete_set_membership_downward_closed:
  shows \<open>(a,b) \<in> set (adelete ks k) \<Longrightarrow> a \<noteq> k \<Longrightarrow> (a,b) \<in> set ks\<close>
  by (induct ks k rule: adelete.induct) (auto simp: split: if_splits)

lemma adelete_salist_inv_preserve:
  shows \<open>salist_inv ks \<Longrightarrow> salist_inv (adelete ks k)\<close>
proof (induct ks k rule: adelete_induct)
  case (ANil k)
  then show ?case by auto
next
  case (ACons m q ks k)
  have False if \<open>m \<noteq> k\<close> and \<open>(m, b) \<in> set (adelete ks k)\<close> for b 
  proof -
    have \<open>(m,b) \<in> set ks\<close>
      by (meson adelete_set_membership_downward_closed that)
    then have \<open>\<not> distinct (map fst ((m, q) # ks))\<close>
      using ACons.prems adelete_deletes_keys by fastforce
    then show False
      using ACons.prems salist_invE by blast
  qed
  moreover have False if \<open>m > a\<close> \<open>m \<noteq> k\<close> and \<open>(a, b) \<in> set (adelete ks k)\<close> for a b
  proof -
    have \<open>(a,b) \<in> set ks\<close>
      using that adelete_set_membership_downward_closed
      by (metis ACons.prems adelete_deletes_keys fst_conv image_iff salist_Cons_downward_closedD)
    then have \<open>\<not> sorted (map fst ((m, q) # ks))\<close>
      using \<open>m > a\<close> by fastforce
    then show False
      using ACons.prems salist_invE by blast
  qed
  ultimately show ?case
    using ACons leI by (force simp: salist_inv_def)
qed

lemma map_of_adelete_eq [simp]:
  shows \<open>salist_inv ks \<Longrightarrow> map_of (adelete ks k) k = None\<close>
  by (simp add: adelete_deletes_keys map_of_eq_None_iff)

lemma map_of_adelete_neq [rule_format, simp]:
  shows \<open>salist_inv ks \<Longrightarrow> k \<noteq> k' \<Longrightarrow> map_of (adelete ks k) k' = map_of ks k'\<close>
  by (induct ks k rule: adelete_induct) (auto dest: salist_Cons_downward_closedD)

subsection\<open>Data structure\<close>

text\<open>These are maps with a canonical representation: equality of the mapping implies equality of the
datastructure, and \<^emph>\<open>vice versa\<close>.\<close>

typedef (overloaded) ('k, 'v) salist =
    \<open>{ m::('k::{linorder} \<times> 'v) list. salist_inv m }\<close>
  by (rule_tac x=\<open>[]\<close> in exI, force simp add: salist_inv_def)

setup_lifting type_definition_salist

instantiation salist :: (linorder, equal)equal
begin

lift_definition equal_salist :: \<open>('a, 'b) salist \<Rightarrow> ('a, 'b) salist \<Rightarrow> bool\<close> is
  \<open>\<lambda>s t. s = t\<close> .

instance
  apply standard
  apply transfer
  apply (auto simp add: equal_salist_def)
  done

end

lift_definition empty :: \<open>('k::{linorder}, 'v) salist\<close> is \<open>[]\<close>
  by (auto simp add: salist_inv_def)

lift_definition is_empty :: \<open>('k::{linorder}, 'v) salist \<Rightarrow> bool\<close> is \<open>\<lambda>s. s = []\<close> .

lemma is_empty_empty [intro]:
  shows \<open>is_empty empty\<close>
  by transfer simp

lift_definition lookup :: \<open>('k::{linorder}, 'v) salist \<Rightarrow> 'k \<Rightarrow> 'v option\<close>
  is \<open>\<lambda>s k. map_of s k\<close> .

lemma lookup_empty_None [simp]:
  shows \<open>lookup empty k = None\<close>
  by transfer force

lemma is_empty_ext_None [intro]:
  assumes \<open>\<And>k .lookup m k = None\<close>
  shows \<open>is_empty m\<close>
using assms by transfer (meson map_of_eq_empty_iff)

lemma nonempty_index [elim]:
  assumes \<open>\<not>is_empty m\<close>
  obtains k x where \<open>lookup m k = Some x\<close>
  using assms by fastforce

lemma salist_inv_map_of_implies_eq:
  assumes \<open>salist_inv m\<close>
    and \<open>salist_inv n\<close>
    and \<open>map_of m = map_of n\<close>
    shows \<open>m = n\<close>
  using assms
proof(induction m arbitrary: n)
  case Nil
  then show ?case by force
next
  case (Cons x m n0)
  then obtain a b c d n where \<open>x = (a,b)\<close> \<open>n0 = Cons (c,d) n\<close>
    by (metis empty_eq_map_of_iff list.exhaust surj_pair)
  with Cons show ?case
    apply (simp add: salist_inv_def fun_eq_iff map_of_eq_None_iff nle_le)
    by (metis Some_eq_map_of_iff fst_conv map_of_eq_None_iff nle_le option.sel)
qed

lemma lookup_ext [simp]:
  shows \<open>(lookup m = lookup n) \<longleftrightarrow> m = n\<close>
  by transfer (use salist_inv_map_of_implies_eq in blast)

lift_definition insert :: \<open>('k::{linorder}, 'v) salist \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) salist\<close>
  is \<open>\<lambda>s k v. ainsert s k v\<close>
  by (rule ainsert_salist_inv_preserve)

lemma lookup_insert_eq [simp]:
  shows \<open>lookup (insert ks k v) k = Some v\<close>
  by transfer simp

lemma lookup_insert_neq [simp]:
  assumes \<open>k \<noteq> k'\<close>
  shows \<open>lookup (insert ks k v) k' = lookup ks k'\<close>
using assms by transfer simp

lemma lookup_insertE [elim]:
  assumes \<open>lookup (insert ks k v) k' = r\<close>
  and \<open>k = k' \<Longrightarrow> Some v = r  \<Longrightarrow> R\<close>
  and \<open>k \<noteq> k' \<Longrightarrow> lookup ks k' = r \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by force

lift_definition delete :: \<open>('k::{linorder}, 'v) salist \<Rightarrow> 'k \<Rightarrow> ('k, 'v) salist\<close>
  is \<open>\<lambda>s k. adelete s k\<close>
  by (rule adelete_salist_inv_preserve)

lemma lookup_delete_eq [simp]:
  shows \<open>lookup (delete ks k) k = None\<close>
  by transfer simp

lemma lookup_delete_neq [simp]:
  assumes \<open>k \<noteq> k'\<close>
  shows \<open>lookup (delete ks k) k' = lookup ks k'\<close>
  using assms by transfer simp

lemma lookup_deleteE [elim]:
  assumes \<open>lookup (delete ks k) k' = r\<close>
  and \<open>k = k' \<Longrightarrow> r = None \<Longrightarrow> R\<close>
  and \<open>k \<noteq> k' \<Longrightarrow> lookup ks k' = r \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (transfer, auto, blast)

lemma salist_insert_not_empty [simp]:
  \<open>\<not> is_empty (insert sa k x)\<close>
  apply transfer
  by (metis map_of_Cons_code(1) map_of_ainsert_eq option.discI)

text\<open>@{typ \<open>('a, 'b) salist\<close>}s are somewhat tricky to work with in a clean manner. As an alternative
  to using \<^verbatim>\<open>transfer\<close>, we prove a tailored induction principle.\<close>
lemma salist_induction:
  fixes y :: \<open>('a::{linorder}, 'b) salist\<close>
    and P :: \<open>('a, 'b) salist \<Rightarrow> bool\<close>
  assumes \<open>P (Abs_salist [])\<close>
    and \<open>\<And> k v y. 
            \<comment> \<open>We keep the @{term salist_inv} terms so that @{thm Abs_salist_inverse} remains usable\<close>
              salist_inv ((k, v) # y) \<Longrightarrow> salist_inv y \<Longrightarrow> 
              P (Abs_salist y) \<Longrightarrow>
              k \<notin> fst ` set y \<Longrightarrow> distinct (list.map fst y) \<Longrightarrow> (\<forall>x\<in>set y. k \<le> fst x) \<Longrightarrow> sorted (list.map fst y) \<Longrightarrow>
              P (Abs_salist ((k, v) # y))\<close>
  shows \<open>P y\<close>
proof -
  {
    fix y :: \<open>('a \<times> 'b) list\<close>
    assume \<open>salist_inv y\<close>
    from this assms have \<open>P (Abs_salist y)\<close>
      by (induction y; simp add: salist_inv_def fst_def split: prod.splits)
  }
  then show ?thesis
    by (cases y, simp)
qed

lemma salist_inv_nil [simp]:
  shows \<open>salist_inv []\<close>
  by (simp add: salist_inv_def)

end