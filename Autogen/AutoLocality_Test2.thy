(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test2
  imports AutoLens AutoLocality AutoLocality_Test0 AutoLocality_Test1 
begin
(*>*)

locality_lemma for AutoLocality_Test0.TestRec:
  AutoLocality_Test0.test_get0 footprint [my_field0] .
locality_lemma for AutoLocality_Test1.test_rec:
  AutoLocality_Test1.test_get0 footprint [my_field0] .
locality_lemma for AutoLocality_Test0.test_rec':
  AutoLocality_Test0.test_get0' footprint [my_field0] .
locality_lemma for AutoLocality_Test1.test_rec':
  AutoLocality_Test1.test_get0' footprint [my_field0] .

print_locality_data

(*<*)
end
(*>*)