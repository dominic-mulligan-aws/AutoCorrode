(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory BraunTreeAdditional
  imports BraunTrees
begin

text\<open>Additional operations and proofs on Braun trees not already found in the Isabelle
standard library (or our in-tree copy of it).\<close>

fun tree_map :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b tree\<close> where
  \<open>tree_map f Leaf = Leaf\<close> |
  \<open>tree_map f (Node l x r) = Node (tree_map f l) (f x) (tree_map f r)\<close>

lemma tree_map_size [simp]:
  shows \<open>size (tree_map f t) = size t\<close>
by (induction t) auto

lemma tree_map_braun [intro]:
  assumes \<open>braun t\<close>
    shows \<open>braun (tree_map f t)\<close>
using assms by (induction t) auto

lemma tree_map_lookup1_aux:
  assumes \<open>i \<le> size t\<close> and \<open>braun t\<close> and \<open>i \<noteq> 0\<close>
  shows \<open>lookup1 (tree_map f t) i = f (lookup1 t i)\<close>
  using assms
proof (induction t i arbitrary: rule: lookup1.induct)
  case (1 l x r n)
  show ?case
  proof (cases \<open>n div 2 \<le> size r\<close>)
    case True
    with 1 show ?thesis by auto
  next
    case False
    with 1 show ?thesis
      using le_Suc_eq by fastforce
  qed
qed auto

lemma tree_map_lookup1:
  assumes \<open>i < size t\<close> and \<open>braun t\<close>
    shows \<open>lookup1 (tree_map f t) (Suc i) = f (lookup1 t (Suc i))\<close>
  by (simp add: Suc_le_eq assms tree_map_lookup1_aux)

fun braun_take :: \<open>'a tree \<Rightarrow> nat \<Rightarrow> 'a tree\<close> where
  \<open>braun_take Leaf 0 = Leaf\<close> |
  \<open>braun_take (Node l v r) 0 = Leaf\<close> |
  \<open>braun_take Leaf (Suc n) = Leaf\<close> |
  \<open>braun_take (Node l v r) (Suc n) =
     Node (braun_take l ((Suc n) div 2)) v (braun_take r (n div 2))\<close>

fun braun_drop :: \<open>'a tree \<Rightarrow> nat \<Rightarrow> 'a tree\<close> where
  \<open>braun_drop Leaf 0 = Leaf\<close> |
  \<open>braun_drop (Node l v r) 0 = Node l v r\<close> |
  \<open>braun_drop Leaf (Suc n) = Leaf\<close> |
  \<open>braun_drop (Node l v r) (Suc n) = braun_drop (merge l r) n\<close>

lemma size_braun_take:
  assumes \<open>braun t\<close>
  shows \<open>size (braun_take t n) = min n (size t)\<close>
  using assms 
proof (induction t n rule: braun_take.induct)
  show \<open>size (braun_take Leaf 0) = min 0 (size Leaf)\<close>
    by clarsimp
next
  fix l v and r :: \<open>'a tree\<close>
  show \<open>size (braun_take (Node l v r) 0) = min 0 (size (Node l v r))\<close>
    by clarsimp
next
  fix n
  show \<open>size (braun_take Leaf (Suc n)) = min (Suc n) (size Leaf)\<close>
    by clarsimp
next
  fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
    and \<open>braun l \<Longrightarrow> size (braun_take l (Suc n div 2)) = min (Suc n div 2) (size l)\<close>
    and \<open>braun r \<Longrightarrow> size (braun_take r (n div 2)) = min (n div 2) (size r)\<close>
  moreover from this have \<open>size (braun_take l (Suc n div 2)) = min (Suc n div 2) (size l)\<close>
    by clarsimp
  moreover from calculation have \<open>size (braun_take r (n div 2)) = min (n div 2) (size r)\<close>
    by clarsimp
  moreover from calculation have \<open>min (Suc n div 2) (size l) + min (n div 2) (size r) = min n (size l + size r)\<close>
    by (auto simp add: min_def)
  ultimately show \<open>size (braun_take (Node l v r) (Suc n)) = min (Suc n) (size (Node l v r))\<close>
    by clarsimp
qed

lemma braun_braun_take:
  assumes \<open>braun t\<close>
    shows \<open>braun (braun_take t n)\<close>
using assms proof (induction t n rule: braun_take.induct)
  show \<open>braun (braun_take Leaf 0)\<close>
    by clarsimp
next
   fix l v and r :: \<open>'a tree\<close>
  show \<open>braun (braun_take (Node l v r) 0)\<close>
    by clarsimp
next
   fix n
  show \<open>braun (braun_take Leaf (Suc n))\<close>
    by clarsimp
next
     fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
     and \<open>braun l \<Longrightarrow> braun (braun_take l (Suc n div 2))\<close>
     and \<open>braun r \<Longrightarrow> braun (braun_take r (n div 2))\<close>
  from this show \<open>braun (braun_take (Node l v r) (Suc n))\<close>
    by (auto simp add: size_braun_take)
qed

lemma splice_take:
  assumes \<open>length l = length r \<or> length l = Suc (length r)\<close>
    shows \<open>splice (take (Suc n div 2) l) (take (n div 2) r) = take n (splice l r)\<close>
using assms proof (induction l r arbitrary: n rule: splice.induct)
  case (1 ys)
  then show ?case by clarsimp
next
  case (2 x xs ys n)
  then show ?case by (cases n; auto)
qed

lemma list_braun_take:
  assumes \<open>braun t\<close>
    shows \<open>braun_list (braun_take t n) = take n (braun_list t)\<close>
using assms proof (induction t n rule: braun_take.induct)
  show \<open>braun_list (braun_take Leaf 0) = take 0 (braun_list Leaf)\<close>
    by clarsimp
next
   fix l v and r :: \<open>'a tree\<close>
  show \<open>braun_list (braun_take (Node l v r) 0) = take 0 (braun_list (Node l v r))\<close>
    by clarsimp
next
   fix n
  show \<open>braun_list (braun_take Leaf (Suc n)) = take (Suc n) (braun_list Leaf)\<close>
    by clarsimp
next
     fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
     and \<open>braun l \<Longrightarrow> braun_list (braun_take l (Suc n div 2)) = take (Suc n div 2) (braun_list l)\<close>
     and \<open>braun r \<Longrightarrow> braun_list (braun_take r (n div 2)) = take (n div 2) (braun_list r)\<close>
  from this show \<open>braun_list (braun_take (Node l v r) (Suc n)) = take (Suc n) (braun_list (Node l v r))\<close>
    by (auto simp add: splice_take size_list)
qed

lemma braun_take_lookup1:
  assumes \<open>braun t\<close>
      and \<open>i < min n (size t)\<close>
    shows \<open>lookup1 (braun_take t n) (Suc i) = lookup1 t (Suc i)\<close>
using assms by (metis Suc_eq_plus1 min_less_iff_conj size_braun_take list_braun_take
  nth_list_lookup1 braun_braun_take nth_take)

lemma merge_size:
  shows \<open>size (merge l r) = size l + size r\<close>
by (induction l r rule: merge.induct) auto

lemma size_braun_drop:
  assumes \<open>braun t\<close>
    shows \<open>size (braun_drop t n) = size t - n\<close>
using assms proof (induction t n rule: braun_drop.induct)
  show \<open>size (braun_drop Leaf 0) = size Leaf - 0\<close>
    by clarsimp
next
   fix l v and r :: \<open>'a tree\<close>
  show \<open>size (braun_drop (Node l v r) 0) = size (Node l v r) - 0\<close>
    by clarsimp
next
   fix n
  show \<open>size (braun_drop Leaf (Suc n)) = size Leaf - Suc n\<close>
    by clarsimp
next
  fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
     and \<open>braun (merge l r) \<Longrightarrow> size (braun_drop (merge l r) n) = size (merge l r) - n\<close>
  from this show \<open>size (braun_drop (Node l v r) (Suc n)) = size (Node l v r) - Suc n\<close>
    by (clarsimp simp add: merge_size braun_merge)
qed

lemma braun_braun_drop:
  assumes \<open>braun t\<close>
    shows \<open>braun (braun_drop t n)\<close>
using assms proof (induction t n rule: braun_drop.induct)
     fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
     and \<open>braun (merge l r) \<Longrightarrow> braun (braun_drop (merge l r) n)\<close>
  from this show \<open>braun (braun_drop (Node l v r) (Suc n))\<close>
    by (clarsimp simp add: braun_merge)
qed auto

lemma list_braun_drop:
  assumes \<open>braun t\<close>
  shows \<open>braun_list (braun_drop t n) = drop n (braun_list t)\<close>
using assms proof (induction t n rule: braun_drop.induct)
     fix l v and r :: \<open>'a tree\<close> and n
  assume \<open>braun (Node l v r)\<close>
     and \<open>braun (merge l r) \<Longrightarrow> braun_list (braun_drop (merge l r) n) = drop n (braun_list (merge l r))\<close>
  from this show \<open>braun_list (braun_drop (Node l v r) (Suc n)) = drop (Suc n) (braun_list (Node l v r))\<close>
    by (clarsimp simp add: braun_merge merge_size list_merge)
qed auto

lemma lookup1_adds:
  assumes \<open>braun xs\<close>
      and \<open>size xs = n\<close>
      and \<open>i < size xs + length l\<close>
    shows \<open>lookup1 (adds l n xs) (Suc i) = (braun_list xs @ l) ! i\<close>
using assms by (metis Suc_eq_plus1 list_adds nth_list_lookup1 size_braun_adds)

text\<open>Braun trees have unique representations\<close>
lemma braun_tree_ext:
  assumes \<open>\<And>i. i < size y \<Longrightarrow> lookup1 x (Suc i) = lookup1 y (Suc i)\<close>
      and \<open>braun x\<close>
      and \<open>braun y\<close>
      and \<open>size x = size y\<close>
    shows \<open>x = y\<close>
using assms proof (induction x arbitrary: y)
  case Leaf
  then show ?case by clarsimp
next
  case Nodex: (Node xl xn xr)
  show ?case
    proof (cases y)
      case Leaf
      from this Nodex show ?thesis by clarsimp
    next
      case (Node yl yn yr)
      { fix i
        assume \<open>i < size yl\<close>
        then have \<open>lookup1 xl (Suc i) = lookup1 yl (Suc i)\<close>
          using Node Nodex Nodex(3)[of \<open>Suc (2*i)\<close>] by (clarsimp, linarith)
      } moreover
      { fix i
        assume \<open>i < size yr\<close>
        then have \<open>lookup1 xr (Suc i) = lookup1 yr (Suc i)\<close>
          using Node Nodex Nodex(3)[of \<open>2*(Suc i)\<close>] by (clarsimp, linarith)
      }
      moreover note Node Nodex
      ultimately show ?thesis by force
    qed
qed

end