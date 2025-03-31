(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Physical_Memory_Trie_PP
  imports Raw_Physical_Memory_Trie
begin

syntax 
  "_tag_mem_content" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close>
  "_mem_node" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close>
  "_mem_constant" :: \<open>logic \<Rightarrow> logic\<close>
  "_mem_tagged_constant" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close>
  "_mem_unknown_tag" :: logic
  "_mem_constant_region" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close>
  "_mem_unknown_region" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close>
  "_mem_marker" :: \<open>logic \<Rightarrow> logic\<close>

  "_mem_regions" :: \<open>logic \<Rightarrow> logic\<close> ("MEMORY \<lparr>' _' \<rparr>")
  "_mem_constant_region" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<lbrakk>_-_\<rbrakk>: _")
  "_mem_data_region" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<lbrakk>_-_\<rbrakk>: [_]")
  "_mem_unknown_region"  :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<lbrakk>_-_\<rbrakk>: UNKNOWN '(_')")
  "_mem_unmapped_region" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<lbrakk>_-_\<rbrakk>: UNMAPPED")

translations
  \<comment>\<open>Phase 1: Map HOL constants to syntax constants\<close>
  "_tag_mem_content t mc" \<leftharpoondown> "CONST MT_tagged a t mc"
  "_mem_node a b" \<leftharpoondown> "CONST MT_node a b"
  "_mem_node a b" \<leftharpoondown> "CONST MC_node a b"
  "_mem_constant v" \<leftharpoondown> "CONST MC_byte v"
  "_mem_marker v" \<leftharpoondown> "CONST Abs_tagged_physical_memory v"

  \<comment>\<open>Phase 2: Merge tag into memory contents\<close>
  "_mem_constant val" \<leftharpoondown> "_mem_tagged_constant (CONST Unity) val"
  "_mem_tagged_constant t val" \<leftharpoondown> "_tag_mem_content t (_mem_constant val)"
  "_mem_node (_tag_mem_content t left) (_tag_mem_content t right)" \<leftharpoondown> "_tag_mem_content t (_mem_node left right)"

ML\<open>
  datatype memory_content_reflected = 
     mc_node of memory_content_reflected * memory_content_reflected
   | mc_constant of Ast.ast
   | mc_unknown of Ast.ast

  datatype memory_region_reflected = 
     mr_constant of int * int * Ast.ast
   | mr_data of int * Ast.ast list
   | mr_unknown of int * int * Ast.ast

  fun reflect_mc_ast (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_mem_node\<close>, l, r]) =
     mc_node (reflect_mc_ast l, reflect_mc_ast r)
   | reflect_mc_ast (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_mem_constant\<close>, v]) =
     mc_constant v
   | reflect_mc_ast x = mc_unknown x

  fun flatten_reflected_mc base width (mc_unknown t) = [mr_unknown (base, width, t)]
    | flatten_reflected_mc base width (mc_constant t) = 
         if width < 16 then
           [mr_data (base, List.tabulate (width, K t ))]
         else
           [mr_constant (base, width, t)]
    | flatten_reflected_mc base width (mc_node (l, r)) = 
        let val fl = flatten_reflected_mc base (width div 2) l 
            val fr = flatten_reflected_mc (base + (width div 2)) (width div 2) r
        in fl @ fr end

  fun reduce_reflected_mr ((x as mr_constant (b0, w0, t0)) :: (xs as (mr_constant (_, w1, t1)) :: xss))
     = (if t0 = t1 then
         reduce_reflected_mr ((mr_constant (b0, w0 + w1, t0)) :: xss)
       else
         x :: (reduce_reflected_mr xs))
   | reduce_reflected_mr (mr_data (b0, t0s) :: (mr_data (_, t1s) :: xss))
     = reduce_reflected_mr ((mr_data (b0, t0s @ t1s)) :: xss)
   | reduce_reflected_mr (x :: xs) = x :: (reduce_reflected_mr xs)
   | reduce_reflected_mr xs = xs

  fun num_to_hex_str num =
    "0x" ^ (Int.fmt StringCvt.HEX num)

  fun numeral_to_ast n = Ast.Appl [Ast.Constant @{syntax_const "_Numeral"}, 
      Ast.Constant (num_to_hex_str n)]

  fun reembed_region (mr_unknown (base, width, t))
      = Ast.Appl [Ast.Constant @{syntax_const "_mem_unknown_region"}, 
         numeral_to_ast base, numeral_to_ast (base + width), t]
    | reembed_region (mr_constant (base, width, t))
      = Ast.Appl [Ast.Constant @{syntax_const "_mem_constant_region"}, 
         numeral_to_ast base, numeral_to_ast (base + width), t]
    | reembed_region (mr_data (base, ts))
      = Ast.Appl [Ast.Constant @{syntax_const "_mem_data_region"},
          numeral_to_ast base, numeral_to_ast (base + length ts),
          Ast.fold_ast @{syntax_const "_args"} ts]

  fun reembed_regions ls = Ast.fold_ast @{syntax_const "_args"} (map reembed_region ls)
\<close>

print_ast_translation \<open>
  let
    fun pmem_ast_tr' [pmem] =
      let val reflected = pmem 
        |> reflect_mc_ast
        |> flatten_reflected_mc 0 (Integer.pow 48 2)
        |> reduce_reflected_mr
        |> reembed_regions 
      in Ast.Appl [Ast.Constant @{syntax_const "_mem_regions"}, reflected] end
  in [(\<^syntax_const>\<open>_mem_marker\<close>, K pmem_ast_tr')] end
\<close>

end