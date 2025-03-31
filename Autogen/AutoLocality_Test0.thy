(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test0
  imports AutoLens AutoLocality
begin
(*>*)

datatype_record foo =
  beef :: nat
  ham :: nat
  cheese :: nat

definition has_beef :: \<open>foo \<Rightarrow> bool\<close> where
  \<open>has_beef f \<equiv> beef f > 0\<close>

definition has_beef_many :: \<open>foo \<Rightarrow> foo \<Rightarrow> bool\<close> where
  \<open>has_beef_many x y \<equiv> beef x > 0\<close>

definition has_ham :: \<open>foo \<Rightarrow> bool\<close> where
  \<open>has_ham f \<equiv> ham f > 0\<close>

definition has_beef2 :: \<open>foo \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>has_beef2 f n \<equiv> beef f > n\<close>

definition set_beef :: \<open>nat \<Rightarrow> foo \<Rightarrow> foo\<close> where
  \<open>set_beef k \<equiv> update_beef (\<lambda>_. k)\<close>

definition set_ham :: \<open>nat \<Rightarrow> foo \<Rightarrow> foo\<close> where
  \<open>set_ham k \<equiv> update_ham (\<lambda>_. k)\<close>

definition set_ham2 :: \<open>foo \<Rightarrow> nat \<Rightarrow> foo\<close> where
  \<open>set_ham2 n k \<equiv> update_ham (\<lambda>_. k) n\<close>

abbreviation set_cheese :: \<open>nat \<Rightarrow> foo \<Rightarrow> foo\<close> where
  \<open>set_cheese k \<equiv> update_cheese (\<lambda>_. k)\<close>

definition set_cheese2 :: \<open>foo \<Rightarrow> nat \<Rightarrow> foo\<close> where
  \<open>set_cheese2 n k \<equiv> update_cheese (\<lambda>_. k) n\<close>

locality_lemma for foo: \<open>set_ham\<close> footprint [ham] .
locality_lemma for foo: \<open>set_beef\<close> footprint [beef] .

print_theorems

locality_lemma for foo: \<open>has_beef\<close> footprint [beef] .
locality_lemma for foo: \<open>has_beef_many\<close> [0] footprint [beef] .
locality_lemma for foo: \<open>has_beef_many\<close> [1] footprint [beef] .

print_theorems
print_locality_data

locality_lemma for foo: \<open>has_ham\<close> footprint [ham] .

print_theorems

locality_autoderive

print_theorems

locality_autoderive

print_theorems

print_locality_data for foo

locality_check

locality_lemma for foo: \<open>has_beef2\<close> footprint [beef] .
locality_lemma for foo: \<open>set_cheese 10\<close> footprint [cheese, beef] .
locality_lemma for foo: \<open>set_cheese2\<close> footprint [cheese] .

print_theorems

locality_check

locality_autoderive for foo

datatype_record ('a, 'b) foo2 =
  beef :: 'a
  ham :: 'b
  cheese :: 'b

local_setup \<open>lens_autogen_defs "foo2"\<close>
local_setup \<open>lens_autogen_defining_equations @{attributes []} "foo2"\<close>
local_setup \<open>lens_autogen_prove_lens_validity @{attributes []} "foo2"\<close>
ML \<open>@{term \<open>foo2.beef\<close>}\<close>
local_setup\<open>focus_autogen_make_field_foci @{attributes []} "foo2"\<close>

export_code foo2_beef_focus in OCaml

value [code] \<open>focus_view foo2_beef_focus (make_foo2 (0 :: nat) 0 (0 :: nat))\<close>

definition set_bham :: \<open>'b \<Rightarrow> ('a, 'b) foo2 \<Rightarrow> ('a, 'b) foo2\<close> where
  \<open>set_bham k \<equiv> update_ham (\<lambda>_. k)\<close>
locality_lemma for foo2: set_bham footprint [ham]  .

definition set_bcheese :: \<open>nat \<Rightarrow> ('a, nat) foo2 \<Rightarrow> ('a, nat) foo2\<close> where
  \<open>set_bcheese k \<equiv> update_cheese (\<lambda>_. k)\<close>
locality_lemma for foo2: set_bcheese footprint [cheese] .

print_theorems
print_locality_data
locality_check

print_locality_data

thm AutoLocality_Test0_foo_locality_facts
thm AutoLocality_Test0_foo_commutativity_facts

lemma
  shows \<open>has_ham (set_ham h (set_beef b X)) = has_ham (set_ham h X)\<close>
using [[locality_cancel]] by simp

lemma
  shows \<open>has_ham (set_ham h (foo.update_beef b (set_ham h2 (set_cheese2 (set_cheese2 X d) c)))) =
          has_ham (set_ham h (set_ham h2 X))\<close>
using [[locality_cancel]] by simp

locale foo_locale =
    fixes some_fun :: \<open>'a \<Rightarrow> 'a\<close>
  assumes some_fun_invo: \<open>some_fun \<circ> some_fun = id\<close>
begin

definition map_beef_via_fun :: \<open>('a, 'a) foo2 \<Rightarrow> ('a, 'a) foo2\<close> where
  \<open>map_beef_via_fun \<equiv> update_beef some_fun\<close>

locality_lemma for foo2: map_beef_via_fun footprint [beef]
  by (auto simp add: map_beef_via_fun_def)

definition map_ham_via_fun :: \<open>('a, 'a) foo2 \<Rightarrow> ('a, 'a) foo2\<close> where
  \<open>map_ham_via_fun \<equiv> update_ham some_fun\<close>

thm map_beef_via_fun_def

locality_lemma for foo2: map_ham_via_fun footprint [ham]
  by (auto simp add: map_ham_via_fun_def)

locality_autoderive for foo2

print_theorems
print_locality_data

end

print_locality_data

context foo_locale
begin

print_locality_data

end

datatype_record TestRec =
  my_field0 :: int
  my_field1 :: int

definition test_get0 :: \<open>TestRec \<Rightarrow> int\<close> where
  \<open>test_get0 r \<equiv> my_field0 r\<close>

context
begin

qualified datatype_record test_rec' =
  my_field0 :: int
  my_field :: int

qualified definition test_get0' :: \<open>test_rec' \<Rightarrow> int\<close> where
  \<open>test_get0' r \<equiv> my_field0 r\<close>

end

(*<*)
end
(*>*)