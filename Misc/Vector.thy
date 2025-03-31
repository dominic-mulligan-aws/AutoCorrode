(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Vector
  imports "HOL-Library.Word" Data_Structures.BraunTreeAdditional ListAdditional
begin
(*>*)

section\<open>A bounded-length vector type\<close>

text\<open>Here we develop a small utility library of bounded vectors.

We use Braun trees to represent the vectors. This gives reasonably
efficient log-time implementations of all the major operations.\<close>

subsection\<open>Supporting lemmas\<close>

lemma lookup1_take_list_fast:
  assumes \<open>braun a\<close>
      and \<open>m \<le> size a\<close>
      and \<open>n < m\<close>
    shows \<open>lookup1 a (Suc n) \<in> set (take m (list_fast a))\<close>
using assms  by (metis (mono_tags, lifting) basic_trans_rules(22) in_set_conv_nth length_take
  list_fast_correct min_less_iff_conj nth_list_lookup1 nth_take semiring_norm(174) size_list)

lemma set_image_take_nth:
  assumes \<open>i < length ls\<close>
      and \<open>i < n\<close>
    shows \<open>f (ls ! i) \<in> f ` set (take n ls)\<close>
using assms by (force intro: imageI simp add: in_set_conv_nth)

lemma set_image_take_nth_elim:
  assumes \<open>f (ls ! i) \<notin> f ` set (take n ls)\<close>
      and \<open>i < length ls\<close> \<open>i < n\<close>
    shows \<open>R\<close>
using assms set_image_take_nth by force

lemma braun_nonempty_butlast:
  assumes \<open>braun a\<close> \<open>size a = Suc n\<close>
  shows \<open>butlast (braun_list a) @ [lookup1 a (size a)] = braun_list a\<close> 
proof -
  have \<open>last (braun_list a) = braun_list a ! n\<close>
    using assms by (metis last_conv_nth list_Nil_iff size_list Zero_not_Suc diff_Suc_1 eq_size_0)
  with nth_list_lookup1[of a n] assms show ?thesis
    by (auto simp: snoc_eq_iff_butlast list_Nil_iff)
qed

subsection\<open>The type itself\<close>

definition is_vector :: \<open>'a tree \<times> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>is_vector x n \<equiv> braun (fst x) \<and> size (fst x) = snd x \<and> snd x \<le> n\<close>

typedef (overloaded) ('a, 'b::\<open>{len}\<close>) vector =
  \<open>{ x::('a tree \<times> nat). is_vector x LENGTH('b) }\<close>
proof -
  have \<open>(Leaf, 0) \<in> {x. is_vector x LENGTH('b)}\<close>
    by (clarsimp simp add: is_vector_def)
  from this show ?thesis
    by blast
qed

(*<*)
setup_lifting vector.type_definition_vector

text\<open>The following is needed to explain to the code-generator how equalities at type \<^verbatim>\<open>vector\<close>
should be treated (basically, use the underlying equality on braun trees):\<close>
instantiation vector :: (equal, len) equal
begin

lift_definition equal_vector :: \<open>('a, 'b::len) vector \<Rightarrow> ('a, 'b) vector \<Rightarrow> bool\<close>
  is \<open>(=)\<close> .

instance
  by standard (simp add: equal_vector_def Rep_vector_inject)

end
(*>*)

subsection\<open>Lifted operations on vectors\<close>

lift_definition vector_len :: \<open>('a, 'b::{len}) vector \<Rightarrow> nat\<close> is \<open>snd\<close> .

lift_definition vector_map :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::{len}) vector \<Rightarrow> ('c, 'b) vector\<close> is
  \<open>\<lambda>f (t,n). (tree_map f t, n)\<close>
by (auto simp add: is_vector_def split: prod.splits)

lift_definition vector_nth :: \<open>('a, 'b::{len}) vector \<Rightarrow> nat \<Rightarrow> 'a\<close> is \<open>\<lambda>(t, n) i. lookup1 t (i+1)\<close> .

lift_definition vector_update :: \<open>('a, 'b::{len}) vector \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a, 'b) vector\<close> is
  \<open>\<lambda>(t, n) i x. if i < n then (update1 (Suc i) x t, n) else (t, n)\<close>
by (auto simp add: is_vector_def braun_update1 size_update1)

lift_definition vector_new :: \<open>('a, 'b::{len}) vector\<close> is
  \<open>(Leaf, 0)\<close>
by (simp add: is_vector_def)

lift_definition vector_push_raw :: \<open>'a \<Rightarrow> ('a, 'b::{len}) vector \<Rightarrow> ('a, 'b) vector\<close> is
  \<open>\<lambda>v (t,n). if n < LENGTH('b) then (update1 (Suc n) v t, Suc n) else (t,n)\<close>
by (auto simp add: is_vector_def braun_add_hi size_add_hi)

definition vector_push :: \<open>'a \<Rightarrow> ('a, 'b::{len}) vector \<Rightarrow> ('a,'b) vector option\<close> where
  \<open>vector_push \<equiv> \<lambda>v xs. if vector_len xs < LENGTH('b) then Some (vector_push_raw v xs) else None\<close>

lift_definition vector_last :: \<open>('a, 'b::{len}) vector \<Rightarrow> 'a\<close> is \<open>\<lambda>(t,n). lookup1 t n\<close> .

lift_definition vector_pop_raw :: \<open>('a,'b::{len}) vector \<Rightarrow> ('a, 'b) vector\<close> is
  \<open>\<lambda>(t, n). if n > 0 then (del_hi n t, n-1) else (t,n)\<close>
by (auto split: prod.splits simp add: is_vector_def braun_del_hi list_del_hi simp flip: size_list)

definition vector_pop :: \<open>('a, 'b::{len}) vector \<Rightarrow> ('a \<times> ('a, 'b) vector) option\<close> where
  \<open>vector_pop xs \<equiv> if vector_len xs > 0 then Some (vector_last xs, vector_pop_raw xs) else None\<close>

lift_definition vector_to_list :: \<open>('a, 'b::{len}) vector \<Rightarrow> 'a list\<close> is \<open>\<lambda>(t, n). list_fast t\<close> .

lift_definition vector_of_list :: \<open>'a list \<Rightarrow> ('a, 'b::{len}) vector\<close> is
  \<open>\<lambda>l. let v = brauns1 l;
           n = size_fast v
        in if n \<le> LENGTH('b) then (v, n) else (Leaf, 0)\<close>
by (clarsimp simp add:is_vector_def  Let_def) (metis brauns1_correct size_fast)

lemma vector_extI:
    fixes xs ys :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_len xs = vector_len ys\<close>
      and \<open>\<And>i. i < vector_len xs \<Longrightarrow> vector_nth xs i = vector_nth ys i\<close>
    shows \<open>xs = ys\<close>
using assms by transfer (auto split: prod.splits simp add: is_vector_def braun_tree_ext)

lemma list_of_vector_of_list:
    fixes v :: \<open>('a, 'b::{len}) vector\<close>
  assumes \<open>v = vector_of_list l\<close>
      and \<open>length l \<le> LENGTH('b)\<close>
    shows \<open>vector_to_list v = l\<close>
using assms
  apply transfer
  apply (metis (mono_tags, lifting) brauns1_correct case_prod_conv list_fast_correct size_fast size_list)
  done

lemma vector_new_list [simp]:
  shows \<open>vector_to_list vector_new = []\<close>
by transfer (simp add: list_fast_correct)

lemma vector_len_list [simp]:
  shows \<open>length (vector_to_list xs) = vector_len xs\<close>
by transfer (auto split: prod.splits simp add: list_fast_correct is_vector_def size_list)

lemma vector_nth_list [simp]:
  assumes \<open>i < vector_len xs\<close>
    shows \<open>vector_to_list xs ! i = vector_nth xs i\<close>
using assms by transfer (auto simp add: is_vector_def list_fast_correct nth_list_lookup1)

lemma vector_push_list:
    fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_push x l = Some l'\<close>
    shows \<open>vector_to_list l' = vector_to_list l @ [x]\<close>
using assms unfolding vector_push_def by transfer (auto split: if_splits simp add: is_vector_def
  list_fast_correct list_add_hi)

lemma vector_pop_list:
  fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_pop l = Some (x, l')\<close>
  shows \<open>vector_to_list l = vector_to_list l' @ [x]\<close>
  using assms
  unfolding vector_pop_def
  apply transfer
  apply (auto simp add:  is_vector_def list_fast_correct list_del_hi dest: braun_nonempty_butlast split: nat_diff_split_asm prod.splits)
  done

lemma vector_len_bound [simp]:
  fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  shows \<open>vector_len xs \<le> LENGTH('l)\<close>
by transfer (simp add: is_vector_def)

lemma vector_len_vector_of_list:
  assumes \<open>length xs \<le> LENGTH('l::{len})\<close>
    shows \<open>vector_len ((vector_of_list xs)::('a, 'l) vector) = length xs\<close>
  by (metis assms list_of_vector_of_list vector_len_list)

lemma vector_new_len [simp]:
  shows \<open>vector_len vector_new = 0\<close>
by transfer simp

lemma vector_push_len [simp]:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_push a xs = Some xs'\<close>
    shows \<open>vector_len xs' = vector_len xs + 1\<close>
using assms unfolding vector_push_def by transfer (auto split: if_splits)

lemma vector_pop_len [simp]:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_pop xs = Some (a, xs')\<close>
    shows \<open>vector_len xs = vector_len xs' + 1\<close>
using assms unfolding vector_pop_def by transfer (auto split: if_splits)

lemma vector_update_len [simp]:
  fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  shows \<open>vector_len (vector_update xs i v) = vector_len xs\<close>
by (transfer, auto)

lemma vector_to_list_Nil_vector_len:
  shows \<open>vector_to_list vs \<noteq> [] \<longleftrightarrow> 0 < vector_len vs\<close>
  by (metis length_greater_0_conv vector_len_list)

lemma vector_nth_vector_of_list:
  assumes \<open>i < length xs\<close>
      and \<open>length xs \<le> LENGTH('l::{len})\<close>
    shows \<open>vector_nth ((vector_of_list xs::('a, 'l) vector)) i = xs ! i\<close>
  using assms
  by (metis list_of_vector_of_list vector_len_list vector_nth_list)

lemma vector_map_nth [simp]:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>i < vector_len xs\<close>
    shows \<open>vector_nth (vector_map f xs) i = f (vector_nth xs i)\<close>
using assms by transfer (auto split: prod.splits simp add: is_vector_def tree_map_lookup1)

lemma vector_map_len[simp]:
  shows \<open>vector_len (vector_map f v) = vector_len v\<close>
  by transfer auto

lemma vector_map_comp:
  shows \<open>vector_map f \<circ> vector_map g = vector_map (f \<circ> g)\<close>
    and \<open>vector_map f (vector_map g v) = vector_map (f \<circ> g) v\<close>
  by (intro ext vector_extI; simp)+

lemma vector_map_id[simp]:
  shows \<open>vector_map id = id\<close>
    and \<open>vector_map (\<lambda>x. x) v = v\<close>
  by (intro ext vector_extI; simp)+

lemma vector_nth_update [simp]:
    fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>i < vector_len l\<close>
      and \<open>j < vector_len l\<close>
    shows \<open>vector_nth (vector_update l i v) j = (if i = j then v else vector_nth l j)\<close>
using assms by transfer (auto simp add: lookup1_update1 is_vector_def)


lemma vector_push_nth:
    fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>i \<le> vector_len l\<close>
      and \<open>vector_push x l = Some l'\<close>
    shows \<open>vector_nth l' i = (if i < vector_len l then vector_nth l i else x)\<close>
proof -
  have \<open>lookup1 (update1 (Suc (size a)) x a) (Suc i) = lookup1 a (Suc i)\<close>
    if \<open>braun a\<close> and \<open>braun (update1 (Suc (size a)) x a)\<close> and \<open>i < size a\<close>
    for a 
    using that by (metis Suc_eq_plus1 less_SucI list_add_hi nth_append nth_list_lookup1 size_add_hi size_list)
  moreover have \<open>lookup1 (update1 (Suc (size a)) x a) (Suc (size a)) = x\<close>
    if \<open>braun a\<close> \<open>braun (update1 (Suc (size a)) x a)\<close>
      and \<open>size (update1 (Suc (size a)) x a) = Suc (size a)\<close>
    for a
    using that braun_nonempty_butlast list_add_hi by fastforce
  ultimately show ?thesis
    using assms unfolding vector_push_def
    by transfer (auto simp add: is_vector_def split: if_splits)
qed

lemma vector_push_end [simp]:
    fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_push x l = Some l'\<close>
    shows \<open>vector_nth l' (vector_len l) = x\<close>
using assms vector_push_nth by force

lemma vector_push_nil [simp]:
  fixes l :: \<open>('a, 'l::{len}) vector\<close>
  shows \<open>vector_push x l = None \<longleftrightarrow> vector_len l = LENGTH('l)\<close>
unfolding vector_push_def by transfer (auto split: prod.splits simp add: is_vector_def)

lemma vector_pop_nil [simp]:
  fixes l :: \<open>('a, 'l::{len}) vector\<close>
  shows \<open>vector_pop l = None \<longleftrightarrow> vector_len l = 0\<close>
unfolding vector_pop_def by transfer (auto split: if_splits simp add: is_vector_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma vector_pop_nth:
    notes vector_nth_list [simp del]
      and vector_len_list [simp del]
    fixes l :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>i < vector_len l\<close>
      and \<open>vector_pop l = Some (x, l')\<close>
    shows \<open>vector_nth l i = (if i < vector_len l' then vector_nth l' i else x)\<close>
using assms vector_pop_list[of l x l'] by (auto simp add: nth_append simp flip: vector_nth_list
  vector_len_list)

lemma vector_update_overwrite [simp]:
  assumes \<open>i < vector_len ls\<close>
    shows \<open>vector_update (vector_update ls i v) i w = vector_update ls i w\<close>
using assms by (intro vector_extI) auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma vector_update_swap:
  assumes \<open>i \<noteq> j\<close>
      and \<open>i < vector_len ls\<close>
      and \<open>j < vector_len ls\<close>
    shows \<open>vector_update (vector_update ls i v) j w = vector_update (vector_update ls j w) i v\<close>
using assms by (intro vector_extI) auto

definition vector_nth_opt :: \<open>nat \<Rightarrow> ('a, 'l::{len}) vector \<Rightarrow> 'a option\<close> where
  \<open>vector_nth_opt n v \<equiv> if n < vector_len v then Some (vector_nth v n) else None\<close>

lemma vector_nth_opt_spec:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>n < vector_len xs\<close>
    shows \<open>vector_nth_opt n xs = Some (vector_nth xs n)\<close>
using assms by (simp add: vector_nth_opt_def)

lemma vector_nth_opt_spec2:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_nth_opt n xs = Some v\<close>
    shows \<open>vector_nth xs n = v\<close> and \<open>n < vector_len xs\<close>
using assms by (auto simp add: vector_nth_opt_def split: if_splits)

lemma vector_nth_optE:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>vector_nth_opt n xs = Some v\<close>
      and \<open>vector_nth xs n = v \<Longrightarrow> n < vector_len xs \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms vector_nth_opt_spec2 by metis

lemma vector_nth_optI [intro]:
    fixes xs :: \<open>('a, 'l::{len}) vector\<close>
  assumes \<open>n < vector_len xs\<close>
      and \<open>vector_nth xs n = v\<close>
    shows \<open>vector_nth_opt n xs = Some v\<close>
using assms by (auto simp add: vector_nth_opt_spec)

definition vector_over_nth :: \<open>nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'l::{len}) vector \<Rightarrow> ('a, 'l) vector\<close> where
  \<open>vector_over_nth i f v \<equiv> if i < vector_len v then vector_update v i (f (vector_nth v i)) else v\<close>

lemma vector_over_nth_list_update:
  shows \<open>vector_over_nth n f xs = (if n < vector_len xs then vector_update xs n (f (vector_nth xs n)) else xs)\<close>
by (simp add: vector_over_nth_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma vector_over_nth_list_update':
  shows \<open>vector_over_nth = (\<lambda>n f xs. if n < vector_len xs then vector_update xs n (f (vector_nth xs n)) else xs)\<close>
using vector_over_nth_list_update by blast

lemma vector_over_nth_is_valid:
  shows \<open>vector_nth_opt n (vector_over_nth n f l) = map_option f (vector_nth_opt n l)\<close>
    and \<open>map_option f (vector_nth_opt n l) = vector_nth_opt n l \<Longrightarrow> vector_over_nth n f l = l\<close>
    and \<open>vector_over_nth n f (vector_over_nth n g l) = vector_over_nth n (\<lambda>x. f (g x)) l\<close>
by (auto simp add: vector_over_nth_def vector_nth_opt_def intro: vector_extI)

lemma set_take_vector_to_list:
    fixes vs :: \<open>('a, 'b::{len}) vector\<close>
  assumes \<open>\<exists>n. n < m \<and> vector_nth vs n = x\<close>
      and \<open>m \<le> vector_len vs\<close>
    shows \<open>x \<in> set (take m (vector_to_list vs))\<close>
using assms by transfer (auto simp add: is_vector_def intro!: lookup1_take_list_fast)

lemma set_image_vector_take_vector_nth_elim':
  assumes \<open>f (vector_nth ls i) \<notin> f ` set (take n (vector_to_list ls))\<close>
      and \<open>i < vector_len ls\<close>
      and \<open>i < n\<close>
    shows \<open>R\<close>
using assms
  by (metis set_image_take_nth vector_len_list vector_nth_list)

(*<*)
end
(*>*)