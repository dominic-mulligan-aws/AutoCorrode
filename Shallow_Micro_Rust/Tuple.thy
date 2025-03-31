(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Tuple
  imports
    Core_Expression
begin
(*>*)

datatype tnil = TNil

abbreviation(input) tuple_base_pair :: \<open>('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                        ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                        ('s, 'arg0 \<times> 'arg1 \<times> tnil, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_base_pair \<equiv> bindlift2 (\<lambda>x y. (x, y, TNil))\<close>

abbreviation(input) tuple_cons :: \<open>('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                   ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                   ('s, 'arg0 \<times> 'arg1, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_cons \<equiv> bindlift2 (\<lambda>x y. (x, y))\<close>

abbreviation(input) tuple_index_0 :: \<open>('s, 'arg0 \<times> 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_0 \<equiv> bindlift1 fst\<close>

abbreviation(input) tuple_index_1 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_1 \<equiv> bindlift1 (fst \<circ> snd)\<close>

abbreviation(input) tuple_index_2 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_2 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_3 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_3 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_4 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_4 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_5 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_5 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

(*<*)
end
(*>*)