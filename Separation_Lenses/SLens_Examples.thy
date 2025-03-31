(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory SLens_Examples
  imports
    SLens
    Shallow_Separation_Logic.Share_Map
begin

section \<open>Examples of Separation lenses\<close>

subsection\<open>Basic examples\<close>

subsubsection\<open>Identity and projection to \<^verbatim>\<open>0\<close>\<close>

text \<open>The identity is a separation lens on any separation algebra:\<close>
lemma id_lens_is_slens: \<open>is_valid_slens lens_id\<close>
  by (clarsimp simp add: is_valid_slens_def is_valid_lens_def lens_modify_def 
    lens_id_def)

text \<open>The projection to the \<^verbatim>\<open>0\<close> separation algebra \<^verbatim>\<open>()\<close> is a separation lens:\<close>

lemma zero_lens_is_slens: \<open>is_valid_slens zero_lens\<close>
  by (clarsimp simp add: is_valid_slens_def is_valid_lens_def lens_modify_def 
    zero_lens_def disjoint_unit_def)

text \<open>The projection from a product separation algebra onto one of its factors is a
separation lens:\<close>

definition prod_lens_fst :: \<open>('s \<times> 't, 's) lens\<close> where
  \<open>prod_lens_fst \<equiv> make_lens (fst :: ('s \<times> 't) \<Rightarrow> 's) (\<lambda>y. apfst (\<lambda>_. y))\<close>

definition prod_lens_snd :: \<open>('s \<times> 't, 't) lens\<close> where
  \<open>prod_lens_snd \<equiv> make_lens (snd :: ('s \<times> 't) \<Rightarrow> 't) (\<lambda>y. apsnd (\<lambda>_. y))\<close>

lemma prod_lens_fst_valid: \<open>is_valid_lens prod_lens_fst\<close>
  unfolding is_valid_lens_def prod_lens_fst_def by auto

lemma prod_lens_snd_valid: \<open>is_valid_lens prod_lens_snd\<close>
  unfolding is_valid_lens_def prod_lens_snd_def by auto

lemma prod_slens_fst_valid: \<open>is_valid_slens prod_lens_fst\<close>
  by (auto intro!: is_valid_slensI simp add: prod_lens_fst_def is_valid_lens_def
    disjoint_prod_def plus_prod_def lens_modify_def)

lemma prod_slens_snd_valid: \<open>is_valid_slens prod_lens_snd\<close>
  by (auto intro!: is_valid_slensI simp add: prod_lens_snd_def is_valid_lens_def
    disjoint_prod_def plus_prod_def lens_modify_def)

text \<open>The composition of separation lenses is a separation lens\<close>

context
  fixes slensA :: \<open>('s::sepalg, 't::sepalg) lens\<close>
    and slensB :: \<open>('t::sepalg, 'u::sepalg) lens\<close>
  assumes slensA_valid: \<open>is_valid_slens slensA\<close>
      and slensB_valid: \<open>is_valid_slens slensB\<close>
begin

lemma lensA_valid: \<open>is_valid_lens slensA\<close> using slensA_valid by (auto elim: is_valid_slensE)
lemma lensB_valid: \<open>is_valid_lens slensB\<close> using slensB_valid by (auto elim: is_valid_slensE)
lemma slens_compose_valid:
  shows \<open>is_valid_slens (slensA \<circ>\<^sub>L slensB)\<close>
proof (intro is_valid_slensI)
  show \<open>is_valid_lens (slensA \<circ>\<^sub>L slensB)\<close> 
    by (simp add: compose_lens_is_valid_lens_preserving lensA_valid lensB_valid)
next
  show \<open>\<And>x y. x \<sharp> y \<Longrightarrow> lens_view (slensA \<circ>\<^sub>L slensB) x \<sharp> lens_view (slensA \<circ>\<^sub>L slensB) y\<close>
    by (simp add: compose_lens_components slensA_valid slensB_valid slens.slens_view_local1)
next
  show \<open>\<And>x y. x \<sharp> y \<Longrightarrow>
           lens_view (slensA \<circ>\<^sub>L slensB) (x + y) =
           lens_view (slensA \<circ>\<^sub>L slensB) x + lens_view (slensA \<circ>\<^sub>L slensB) y\<close>
    by (simp add: compose_lens_components slensA_valid slensB_valid slens.slens_view_local1 
      slens.slens_view_local2)
next
  show \<open>\<And>f x y.
       x \<sharp> y \<Longrightarrow>
       f (lens_view (slensA \<circ>\<^sub>L slensB) x) \<sharp> lens_view (slensA \<circ>\<^sub>L slensB) y \<Longrightarrow>
       f (lens_view (slensA \<circ>\<^sub>L slensB) x + lens_view (slensA \<circ>\<^sub>L slensB) y) =
       f (lens_view (slensA \<circ>\<^sub>L slensB) x) + lens_view (slensA \<circ>\<^sub>L slensB) y \<Longrightarrow>
       lens_modify (slensA \<circ>\<^sub>L slensB) f (x + y) = lens_modify (slensA \<circ>\<^sub>L slensB) f x + y\<close>
    using lensA_valid lensB_valid 
    by (clarsimp simp add: compose_lens_components)
     (metis disjoint_sym is_valid_slensE sepalg_comm slensA_valid slensB_valid)
next
  show \<open>\<And>f x y.
       x \<sharp> y \<Longrightarrow>
       f (lens_view (slensA \<circ>\<^sub>L slensB) x) \<sharp> lens_view (slensA \<circ>\<^sub>L slensB) y \<Longrightarrow>
       f (lens_view (slensA \<circ>\<^sub>L slensB) x + lens_view (slensA \<circ>\<^sub>L slensB) y) =
       f (lens_view (slensA \<circ>\<^sub>L slensB) x) + lens_view (slensA \<circ>\<^sub>L slensB) y \<Longrightarrow>
       lens_modify (slensA \<circ>\<^sub>L slensB) f x \<sharp> y\<close>
     using lensA_valid lensB_valid 
    by (clarsimp simp add: compose_lens_components)
     (metis disjoint_sym is_valid_slensE sepalg_comm slensA_valid slensB_valid)
qed

end

text\<open>Evaluation at a fixed key provides a separation lens from share maps to shareable values:\<close>

context
  fixes k :: \<open>'k::linorder\<close>
begin

definition share_map_eval_lens :: \<open>(('k, 'v) rbt_share_map, 'v shareable_value) lens\<close>
  where \<open>share_map_eval_lens \<equiv> make_lens (\<lambda>m. rbt_share_map_\<alpha> m k) (rbt_share_map_update k)\<close>

lemma share_map_eval_lens_valid:
  shows \<open>is_valid_lens share_map_eval_lens\<close>
  by (auto intro!: is_valid_lensI rbt_share_map_eqI simp add: share_map_eval_lens_def)

lemma share_map_eval_slens_valid:
  shows \<open>is_valid_slens share_map_eval_lens\<close>
  using share_map_eval_lens_valid 
  by (auto intro!: is_valid_slensI rbt_share_map_eqI simp add: share_map_eval_lens_def
    disjoint_fun_def plus_fun_def disjoint_rbt_share_map_def)

end

end