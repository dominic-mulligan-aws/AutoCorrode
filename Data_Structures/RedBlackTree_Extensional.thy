(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory RedBlackTree_Extensional
  imports Main "HOL-Library.Word" "HOL-Library.RBT"
begin
(*>*)

text\<open>This theory provides a version of Red-Black-Tree based maps with
extensional equality. It can be used to build efficient separation algebras
for map data structures.\<close>

definition rbt_ext_eq :: \<open>('k::{linorder}, 'v) rbt \<Rightarrow> ('k, 'v) rbt \<Rightarrow> bool\<close> where
  \<open>rbt_ext_eq rm0 rm1 \<equiv> \<forall>v. RBT.lookup rm0 v = RBT.lookup rm1 v\<close>

quotient_type (overloaded) ('k, 'v) rbt_ext = \<open>('k::{linorder}, 'v) rbt\<close> / rbt_ext_eq
  by (auto simp add: equivp_def rbt_ext_eq_def) (metis rbt_ext_eq_def)

lift_definition rbt_ext_bulkload :: \<open>('k::{linorder} \<times> 'v) list \<Rightarrow> ('k, 'v) rbt_ext\<close>
  is \<open>RBT.bulkload\<close> .

lift_definition rbt_ext_entries :: \<open>('k::{linorder}, 'v) rbt_ext \<Rightarrow> ('k \<times> 'v) list\<close> is
  \<open>\<lambda>m. (RBT.entries m)\<close>
using entries_lookup by (force simp add: rbt_ext_eq_def)

abbreviation rbt_ext_set :: \<open>('k::{linorder}, 'v) rbt_ext \<Rightarrow> ('k \<times> 'v) set\<close> where
  \<open>rbt_ext_set m \<equiv> set (rbt_ext_entries m)\<close>

lemma rbt_ext_bulkload_entries:
  assumes \<open>distinct (map fst al)\<close>
    shows \<open>rbt_ext_set (rbt_ext_bulkload al) = set al\<close>
by (metis RBT.distinct_entries RBT.map_of_entries assms lookup_bulkload map_of_inject_set 
  rbt_ext_bulkload.abs_eq rbt_ext_entries.abs_eq)

definition rbt_ext_from_map :: \<open>('k \<Rightarrow> 'v) \<Rightarrow> ('k::{linorder, enum}, 'v) rbt_ext\<close> where
  \<open>rbt_ext_from_map f \<equiv> rbt_ext_bulkload (map (\<lambda>k. (k, f k)) (Enum.enum::'k list))\<close>

definition rbt_ext_constant :: \<open>'v \<Rightarrow> ('k::{linorder, enum}, 'v) rbt_ext\<close> where
  \<open>rbt_ext_constant v \<equiv> rbt_ext_from_map (\<lambda>_. v)\<close>

lift_definition rbt_ext_update :: \<open>'k \<Rightarrow> 'v \<Rightarrow> ('k::{linorder}, 'v) rbt_ext \<Rightarrow> ('k, 'v) rbt_ext\<close> is
  \<open>RBT.insert\<close>
by (simp add: rbt_ext_eq_def)

lift_definition rbt_ext_map_entry :: \<open>'k \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k::{linorder}, 'v) rbt_ext \<Rightarrow>
      ('k, 'v) rbt_ext\<close> is
  \<open>RBT.map_entry\<close>
by (simp add: rbt_ext_eq_def)

lift_definition rbt_ext_delete :: \<open>'k \<Rightarrow> ('k::{linorder}, 'v) rbt_ext \<Rightarrow> ('k, 'v) rbt_ext\<close> is
  \<open>RBT.delete\<close>
by (simp add: rbt_ext_eq_def)

lift_definition rbt_ext_\<alpha> :: \<open>('k::{linorder}, 'v) rbt_ext \<Rightarrow> 'k \<Rightarrow> 'v option\<close>  is
  \<open>RBT.lookup\<close>
by (simp add: rbt_ext_eq_def) blast

lemma rbt_ext_set_alt:
  shows \<open>(k, v) \<in> rbt_ext_set rm \<longleftrightarrow> rbt_ext_\<alpha> rm k = Some v\<close>
by (simp add: lookup_in_tree rbt_ext_\<alpha>.rep_eq rbt_ext_entries.rep_eq)

abbreviation rbt_ext_dom :: \<open>('k::{linorder}, 'v) rbt_ext \<Rightarrow> 'k set\<close> where
  \<open>rbt_ext_dom rm \<equiv> dom (rbt_ext_\<alpha> rm)\<close>

lemma rbt_ext_dest_to_domain:
  shows \<open>fst ` (rbt_ext_set m) = rbt_ext_dom m\<close> (is ?g1)
    and \<open>inj_on fst (rbt_ext_set m)\<close> (is ?g2)
    and \<open>finite (rbt_ext_set m)\<close> (is ?g3)
proof -
  show ?g2
    by (clarsimp simp add: inj_on_def rbt_ext_set_alt)
  show ?g1
    by (metis RBT.map_of_entries dom_map_of_conv_image_fst rbt_ext_\<alpha>.rep_eq rbt_ext_entries.rep_eq)
  from \<open>?g1\<close> \<open>?g2\<close> show ?g3
    by simp
qed

lemma rbt_ext_dom_finite:
  shows \<open>finite (rbt_ext_dom m)\<close> 
by (simp add: rbt_ext_\<alpha>.rep_eq)

definition rbt_ext_lookup :: \<open>'k \<Rightarrow> ('k::{linorder}, 'v) rbt_ext \<Rightarrow> 'v option\<close> where
  \<open>rbt_ext_lookup k rm \<equiv> rbt_ext_\<alpha> rm k\<close>

definition rbt_filter_map :: \<open>('k::{linorder} \<Rightarrow> 'v \<Rightarrow> 'v option) \<Rightarrow> ('k, 'v) rbt \<Rightarrow> ('k, 'v) rbt\<close> where
  \<open>rbt_filter_map f m \<equiv>
     let keep = \<lambda>k v. f k v \<noteq> None;
         map  = \<lambda>k v. the (f k v)
      in RBT.map map (RBT.filter keep m)\<close>

lemma rbt_filter_map_correct:                   
  shows \<open>RBT.lookup (rbt_filter_map f m) k = Option.bind (RBT.lookup m k) (f k)\<close>
by (auto simp add: RBT.lookup_filter rbt_filter_map_def Option.bind_def split!: option.splits)

lift_definition rbt_ext_filter_map :: \<open>('k::{linorder} \<Rightarrow> 'v \<Rightarrow> 'v option) \<Rightarrow> ('k, 'v) rbt_ext \<Rightarrow>
      ('k, 'v) rbt_ext\<close> is
  \<open>rbt_filter_map\<close>
by (simp add: rbt_filter_map_correct rbt_ext_eq_def)

lift_definition rbt_ext_map :: \<open>('k::{linorder} \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> ('k, 'v) rbt_ext \<Rightarrow> ('k, 'w) rbt_ext\<close> is
  \<open>RBT.map\<close>
by (simp add: rbt_ext_eq_def)

lift_definition rbt_ext_combine :: \<open>('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('k::{linorder}, 'v) rbt_ext \<Rightarrow>
    ('k, 'v) rbt_ext \<Rightarrow> ('k, 'v) rbt_ext\<close>
  is \<open>RBT.combine\<close>
by (simp add: rbt_ext_eq_def)

lift_definition rbt_ext_empty :: \<open>('k::{linorder}, 'v) rbt_ext\<close> is \<open>RBT.empty\<close> .

lemma rbt_ext_set_empty [simp]:
  shows \<open>rbt_ext_entries rbt_ext_empty = []\<close> 
    and \<open>rbt_ext_set rbt_ext_empty = {}\<close>
by (auto simp add: RBT.empty_def entries.abs_eq eq_onp_same_args rbt_ext_empty_def
  rbt_ext_entries.abs_eq)

definition rbt_ext_dj :: \<open>('k::{linorder}, 'v) rbt_ext \<Rightarrow> ('k, 'v) rbt_ext \<Rightarrow> bool\<close> where
  \<open>rbt_ext_dj rm0 rm1 \<equiv> rbt_ext_dom rm0 \<inter> rbt_ext_dom rm1 = {}\<close>

lemma rbt_ext_correct:
  shows \<open>rbt_ext_lookup k rm = rbt_ext_\<alpha> rm k\<close>
    and \<open>rbt_ext_\<alpha> (rbt_ext_update k v rm) = (rbt_ext_\<alpha> rm)(k \<mapsto> v)\<close>
    and \<open>rbt_ext_\<alpha> (rbt_ext_map_entry k h rm) k' = 
          (if k = k' then map_option h (rbt_ext_\<alpha> rm k) else rbt_ext_\<alpha> rm k')\<close> 
    and \<open>rbt_ext_\<alpha> (rbt_ext_delete k rm) = (rbt_ext_\<alpha> rm) |` (- {k})\<close>
    and \<open>rbt_ext_\<alpha> (rbt_ext_filter_map g rm) k = Option.bind (rbt_ext_\<alpha> rm k) (g k)\<close>
    and \<open>rbt_ext_\<alpha> rbt_ext_empty = (\<lambda>_. None)\<close>
    and \<open>rbt_ext_\<alpha> (rbt_ext_combine f rm0 rm1) k = 
           combine_options f (rbt_ext_\<alpha> rm0 k) (rbt_ext_\<alpha> rm1 k)\<close>
proof -
  show \<open>rbt_ext_lookup k rm = rbt_ext_\<alpha> rm k\<close>
    by transfer (simp add: rbt_ext_lookup_def)
next
  show \<open>rbt_ext_\<alpha> (rbt_ext_delete k rm) = (rbt_ext_\<alpha> rm) |` (- {k})\<close>
    by transfer (simp add: restrict_complement_singleton_eq)
next
  show \<open>rbt_ext_\<alpha> (rbt_ext_map_entry k h rm) k' = 
      (if k = k' then map_option h (rbt_ext_\<alpha> rm k) 
       else rbt_ext_\<alpha> rm k')\<close> 
    by transfer simp
next
  show \<open>rbt_ext_\<alpha> (rbt_ext_update k v rm) = (rbt_ext_\<alpha> rm)(k \<mapsto> v)\<close>
    by transfer simp
next
  show \<open>rbt_ext_\<alpha> (rbt_ext_filter_map g rm) k = Option.bind (rbt_ext_\<alpha> rm k) (g k)\<close>
    by transfer (simp add: rbt_filter_map_correct)
next
  show \<open>rbt_ext_\<alpha> rbt_ext_empty = (\<lambda>_. None)\<close>
    by transfer simp
next
  show \<open>rbt_ext_\<alpha> (rbt_ext_combine f rm0 rm1) k = 
           combine_options f (rbt_ext_\<alpha> rm0 k) (rbt_ext_\<alpha> rm1 k)\<close>
    by transfer simp
qed

lemma rbt_ext_eqI:
  assumes \<open>rbt_ext_\<alpha> rm0 = rbt_ext_\<alpha> rm1\<close>
    shows \<open>rm0 = rm1\<close>
using assms by transfer (simp add: rbt_ext_eq_def)

lemma rbt_ext_empty_dom_is_empty:
  shows \<open>m = rbt_ext_empty \<longleftrightarrow> rbt_ext_dom m = {}\<close>
by (auto intro!: rbt_ext_eqI simp add: rbt_ext_correct)

lemma rbt_ext_entries_from_map[simp]:
  shows \<open>rbt_ext_set (rbt_ext_from_map f :: ('k::{linorder, enum}, 'v) rbt_ext) =  (\<lambda>k. (k, f k)) ` UNIV\<close>
by (simp add: rbt_ext_from_map_def rbt_ext_bulkload_entries comp_def enum_distinct image_iff
  flip: UNIV_enum)

lemma rbt_ext_\<alpha>_from_map[simp]:
  shows \<open>rbt_ext_\<alpha> (rbt_ext_from_map f :: ('k::{linorder, enum}, 'v) rbt_ext) = Some o f\<close>
by (intro ext, simp flip: rbt_ext_set_alt)

lemma rbt_ext_entries_constant[simp]:
  shows \<open>rbt_ext_set (rbt_ext_constant v :: ('k::{linorder, enum}, 'v) rbt_ext) = 
                (\<lambda>k. (k,v)) ` UNIV\<close>
by (simp add: rbt_ext_constant_def)

lemma rbt_ext_\<alpha>_constant[simp]:
  shows \<open>rbt_ext_\<alpha> (rbt_ext_constant v :: ('k::{linorder, enum}, 'v) rbt_ext) = (\<lambda>_. Some v)\<close>
by (simp add: rbt_ext_constant_def comp_def)

named_theorems rbt_ext_basic

lemma rbt_ext_add_comm[rbt_ext_basic]:
    fixes rm0 rm1 :: \<open>('k::linorder, 'v) rbt_ext\<close>
  assumes \<open>\<forall>k v0 v1. rbt_ext_\<alpha> rm0 k = Some v0 \<longrightarrow> rbt_ext_\<alpha> rm1 k = Some v1 \<longrightarrow> f v0 v1 = f v1 v0\<close>
    shows \<open>rbt_ext_combine f rm0 rm1 = rbt_ext_combine f rm1 rm0\<close>
using assms by (auto simp add: rbt_ext_correct combine_options_def intro!: rbt_ext_eqI
  split!: option.splits)

lemma rbt_ext_add_empty_unit[rbt_ext_basic]:
  shows \<open>rbt_ext_combine f rm0 rbt_ext_empty = rm0\<close>
    and \<open>rbt_ext_combine f rbt_ext_empty rm0 = rm0\<close>
proof -
  show \<open>rbt_ext_combine f rm0 rbt_ext_empty = rm0\<close>
    by (auto simp add: rbt_ext_basic rbt_ext_correct intro!: rbt_ext_eqI) 
  show \<open>rbt_ext_combine f rbt_ext_empty rm0 = rm0\<close>
    by (auto simp add: rbt_ext_basic rbt_ext_correct intro!: rbt_ext_eqI) 
qed

(*<*)
end
(*>*)