(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test1
  imports AutoLens AutoLocality
begin
(*>*)

datatype_record test_rec =
  my_field0 :: int
  my_field1 :: int

definition test_get0 :: \<open>test_rec \<Rightarrow> int\<close> where
  \<open>test_get0 r \<equiv> my_field0 r\<close>

context
begin

qualified datatype_record test_rec' =
  my_field0 :: int
  my_field  :: int

qualified definition test_get0' :: \<open>test_rec' \<Rightarrow> int\<close> where
  \<open>test_get0' r \<equiv> my_field0 r\<close>

end

(*<*)
end
(*>*)