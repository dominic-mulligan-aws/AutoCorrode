(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust_Shallow_Embedding
  imports
    Micro_Rust_Parsing_Frontend.Micro_Rust_Syntax
    Core_Syntax
    Prompts_And_Responses
    "HOL-Library.Datatype_Records"
    Autogen.Autogen
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
    Tuple
  keywords
    "notation_nano_rust"
    "notation_nano_rust_field"
    "notation_nano_rust_function"
    "micro_rust_record" :: thy_decl
begin
(*>*)
section\<open>The shallow embedding of uRust into HOL\<close>

text\<open>In this section we define the shallow embedding of uRust into HOL as
a syntax transformations \<^text>\<open>urust \<Rightarrow> logic\<close> from the syntactic category of Micro Rust programs
to the category of HOL terms.\<close>

subsection\<open>Custom identifiers and identifier remapping\<close>

text\<open>The in-built syntax category \<^verbatim>\<open>id\<close> of HOL identifiers does not encompass qualified
Rust names such as \<^verbatim>\<open>Foo::Bar\<close>. To still be able to use those in Micro Rust, we add a custom
command to register them as keywords in Isabelle's lexer, and add them to \<^verbatim>\<open>urust_identifier\<close> so
they can be used in Micro Rust expressions.

Upon shallow embedding of Micro Rust into HOL, the custom identifiers will be interpreted as a
specified HOL constant which may have the same or a different name \<^emph>\<open>in HOL\<close>. More generally,
we also allow the registration of a Micro-Rust-to-HOL name change for those identifiers which do fall
under the \<^verbatim>\<open>id\<close> syntax category.

We distinguish two remapping contexts: Literals and function expressions. The
command \<^text>\<open>notation_nano_rust\<close> registers a name remapping for identifiers used as literals,
while \<^text>\<open>notation_nano_rust_expression\<close> registers a name remapping for identifiers used as
functions.\<close>

syntax
  "_urust_identifier_id_const" :: \<open>id \<Rightarrow> logic\<close> ("URUST'_CONST _")

parse_ast_translation\<open>
let
  fun urust_const_ast_tr _ [Ast.Variable c] = Ast.Appl [Ast.Constant "_urust_identifier_id", Ast.Constant c]
  | urust_const_ast_tr _ asts = raise Ast.AST ("urust_const_ast_tr", asts)
in
  [(\<^syntax_const>\<open>_urust_identifier_id_const\<close>, urust_const_ast_tr)]
end
\<close>

ML\<open>
   fun notation_nano_rust ty (hol_name, nano_rust_name) = let
     (* If the Nano Rust name is an identifier, we only need to register a translation
        rule which converts it into the respective HOL identifier.

        If the Nano Rust name is not an identifier, for example `Foo::Bar`, then we
        need to first register it as a keyword + custom grammar production for Micro Rust. *)

     (* Ordinary identifier *)
     fun simple_hol_notation_nano_rust ty hol_name nano_rust_name thy: local_theory = (
        let val translation_in = "_shallow_identifier_as_" ^ ty ^ "(URUST_CONST " ^ " " ^ nano_rust_name ^ ")"
            val translation_out = "CONST " ^ hol_name
            val translation = Syntax.Parse_Rule (("logic",translation_in), ("logic",translation_out)) in
        thy |> (Local_Theory.background_theory (Isar_Cmd.translations true [translation]))
     end)

     fun remove_dots long_identifier =
           (long_identifier |> String.explode |> filter (fn c : char => (c <> #".")) |> String.implode)

     (* Complex identifier which needs to be treated as a custom keyword *)
     fun custom_hol_notation_nano_rust ty hol_identifier nano_rust_name thy: local_theory = (
        let val mode = Syntax.mode_default
            val syntax_constant = "_urust_identifier_" ^ (remove_dots hol_identifier)
            val translation_in = "_shallow_identifier_as_" ^ ty ^ " " ^ syntax_constant
            val translation_out = "CONST " ^ hol_identifier
            val translation = Syntax.Parse_Rule (("logic",translation_in), ("logic",translation_out)) in
        thy |> Local_Theory.syntax_cmd true mode [(syntax_constant, "urust_identifier", Mixfix.mixfix nano_rust_name)]
            |> (Local_Theory.background_theory (Isar_Cmd.translations true [translation]))
     end)
  in
    if Symbol_Pos.is_identifier nano_rust_name then
      simple_hol_notation_nano_rust ty hol_name nano_rust_name
    else
      custom_hol_notation_nano_rust ty hol_name nano_rust_name
  end
\<close>

ML\<open>
   \<comment>\<open>TODO: We should actually be able to do the right thing automatically here, by looking at the type
of the HOL constant that's being registered: Fields are lenses, and functions are \<^text>\<open>function_body\<close>'s.\<close>
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust"}
      "Add a named HOL literal to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> (notation_nano_rust "literal"));
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust_field"}
      "Add a named Micro Rust field to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> notation_nano_rust "field");
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust_function"}
      "Add a named Micro Rust function to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> notation_nano_rust "function")
\<close>

named_theorems micro_rust_record_simps
named_theorems micro_rust_record_intros

ML\<open>
   fun number_of_type_arguments ctxt (tyname : string) =
       tyname
    |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
    |> Term.dest_Type
    |> snd
    |> List.length

   fun repeat (_ : 'a) 0 : 'a list = []
     | repeat (x : 'a) n : 'a list = x :: repeat x (n-1)

   fun generic_type_arguments ctxt tyname =
       tyname
    |> number_of_type_arguments ctxt
    |> repeat "type"

   (* Mimicking "instance {rec_name} :: (type, type, ...) localizable .." *)
   fun instantiate_localizable_class rec_name (ctxt : Proof.context) =
     let val typeargs = generic_type_arguments ctxt rec_name in
     ((Class.instance_arity_cmd ([rec_name], typeargs, @{class localizable})
       #> Proof.global_default_proof
       #> Proof_Context.theory_of)
      |> Local_Theory.background_theory) ctxt
     end
\<close>

ML\<open>
   fun register_lens_with_micro_rust rec_name field =
      notation_nano_rust "field" (lens_name rec_name field, field)
   fun register_lenses_with_micro_rust rec_name thy =
      let val fields = get_fields rec_name thy in fold (register_lens_with_micro_rust rec_name) fields thy end

   fun make_lenses (with_fields, rec_name) _ =
       lens_autogen_defs                                                                          rec_name
    #> lens_autogen_defining_equations     @{attributes [micro_rust_record_simps, focus_simps]}   rec_name
    #> lens_autogen_prove_lens_validity    @{attributes [micro_rust_record_intros, focus_intros,
                                                         micro_rust_record_simps, focus_simps]}   rec_name
    #> lens_autogen_prove_update_equations @{attributes [micro_rust_record_simps, focus_simps]}
                                           @{attributes [micro_rust_record_intros, focus_intros]} rec_name
    #> focus_autogen_make_field_foci @{attributes [focus_components]} rec_name
    #> (if with_fields then
          register_lenses_with_micro_rust rec_name
        else
          I)
    #> instantiate_localizable_class rec_name

   val _ =
      Outer_Syntax.local_theory' \<^command_keyword>\<open>micro_rust_record\<close> "make lenses for datatype record"
       (((Scan.optional ((Args.bracks (Args.$$$ "no_fields")) >> K false) true) -- Parse.short_ident) >> make_lenses)
\<close>

subsection\<open>The embedding\<close>

syntax
  \<comment>\<open>The shallow embedding of uRust into HOL\<close>
  "_shallow" :: \<open>urust \<Rightarrow> logic\<close> ("\<lbrakk>_\<rbrakk>"[0]1000)

  \<comment> \<open>Intermediate helper for applying parameters\<close>
  "_shallow_apply_params" :: \<open>logic \<Rightarrow> urust_params \<Rightarrow> logic\<close>

  \<comment> \<open>Intermediate helper for building closures\<close>
  "_shallow_abstract_args" :: \<open>urust_formal_args \<Rightarrow> urust \<Rightarrow> logic\<close>

  \<comment> \<open>Intermediate helper for lowering identifiers to HOL\<close>
  "_shallow_identifier_as_literal" :: \<open>urust_identifier \<Rightarrow> logic\<close>
  "_shallow_identifier_as_function" :: \<open>urust_identifier \<Rightarrow> logic\<close>
  "_shallow_identifier_as_field" :: \<open>urust_identifier \<Rightarrow> logic\<close>

  "_shallow_match_branches" :: \<open>urust_match_branches \<Rightarrow> urust_shallow_match_branches\<close>
  "_shallow_match_branch" :: \<open>urust_match_branch  \<Rightarrow> urust_shallow_match_branch \<close>
  "_shallow_match_pattern" :: \<open>urust_match_pattern \<Rightarrow> urust_shallow_match_pattern\<close>
  "_shallow_match_args" :: \<open>urust_match_pattern_args \<Rightarrow> urust_shallow_match_pattern_args \<close>
  "_shallow_match_arg" :: \<open>urust_match_pattern_arg \<Rightarrow> urust_shallow_match_pattern_arg\<close>
  "_shallow_let_pattern" :: \<open>urust_let_pattern \<Rightarrow> pttrns\<close>
  "_shallow_let_pattern_args" :: \<open>urust_let_pattern_args \<Rightarrow> pttrns\<close>

  "_string_token_to_hol" :: \<open>string_token \<Rightarrow> logic\<close>

text\<open>We define the shallow embedding of uRust into HOL via a series of transformations
at the syntax level.\<close>

context
  notes [[syntax_ast_trace]]
begin
term\<open>let (x, _ :: int) = (5,6) in x+12\<close>
end


translations
  \<comment>\<open>The shallow embedding of a HOL term is the corresponding literal\<close>
  "_shallow(_urust_literal f)"
    \<rightharpoonup> "CONST literal f"
  "_shallow(_urust_fun_literal1 f)"
    \<rightharpoonup> "CONST lift_fun1 f"
  "_shallow(_urust_fun_literal2 f)"
    \<rightharpoonup> "CONST lift_fun2 f"
  "_shallow(_urust_fun_literal3 f)"
    \<rightharpoonup> "CONST lift_fun3 f"
  "_shallow(_urust_fun_literal4 f)"
    \<rightharpoonup> "CONST lift_fun4 f"
  "_shallow(_urust_fun_literal5 f)"
    \<rightharpoonup> "CONST lift_fun5 f"
  "_shallow(_urust_fun_literal6 f)"
    \<rightharpoonup> "CONST lift_fun6 f"
  "_shallow(_urust_fun_literal7 f)"
    \<rightharpoonup> "CONST lift_fun7 f"
  "_shallow(_urust_fun_literal8 f)"
    \<rightharpoonup> "CONST lift_fun8 f"
  "_shallow(_urust_fun_literal9 f)"
    \<rightharpoonup> "CONST lift_fun9 f"
  "_shallow(_urust_fun_literal10 f)"
    \<rightharpoonup> "CONST lift_fun10 f"
  "_shallow(_urust_numeral num)"
    \<rightharpoonup> "CONST literal (_Numeral num)" \<comment>\<open>TODO: What type should we cast numerals to by default?\<close>
  "_shallow(_urust_numeral_0)"
    \<rightharpoonup> "CONST literal 0"
  "_shallow(_urust_numeral_1)"
    \<rightharpoonup> "CONST literal 1"
  "_shallow(_urust_string_token str)"
    \<rightharpoonup> "CONST literal (_string_token_to_hol str)"
  \<comment> \<open>The shallow embedding of a shallow Micro Rust \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> is the expression itself\<close>
  "_shallow(_urust_antiquotation exp)"
    \<rightharpoonup> "exp"
  "_shallow(_urust_unit)"
    \<rightharpoonup> "CONST literal ()"
  "_shallow(_urust_pause)"
    \<rightharpoonup> "CONST pause"
  "_shallow(_urust_log priority logval)"
    \<rightharpoonup> "CONST log priority logval"
  "_shallow(_urust_parens exp)"
    \<rightharpoonup> "_shallow exp"
  \<comment>\<open>Primitive casts\<close>
  "_shallow(_urust_primitive_integral_cast_u8 e)"
    \<rightharpoonup> "CONST ucastu8 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u16 e)"
    \<rightharpoonup> "CONST ucastu16 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u32 e)"
    \<rightharpoonup> "CONST ucastu32 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u64 e)"
    \<rightharpoonup> "CONST ucastu64 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_i32 e)"
    \<rightharpoonup> "CONST ucasti32 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_i64 e)"
    \<rightharpoonup> "CONST ucasti64 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_usize e)"
    \<rightharpoonup> "CONST ucastu64 (_shallow e)"
  "_shallow(_urust_numeral_ascription_0_u8)"
    \<rightharpoonup> "CONST ascribeu8 0"
  "_shallow(_urust_numeral_ascription_1_u8)"
    \<rightharpoonup> "CONST ascribeu8 1"
  "_shallow(_urust_numeral_ascription_u8 e)"
    \<rightharpoonup> "CONST ascribeu8 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u16)"
    \<rightharpoonup> "CONST ascribeu16 0"
  "_shallow(_urust_numeral_ascription_1_u16)"
    \<rightharpoonup> "CONST ascribeu16 1"
  "_shallow(_urust_numeral_ascription_u16 e)"
    \<rightharpoonup> "CONST ascribeu16 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u32)"
    \<rightharpoonup> "CONST ascribeu32 0"
  "_shallow(_urust_numeral_ascription_1_u32)"
    \<rightharpoonup> "CONST ascribeu32 1"
  "_shallow(_urust_numeral_ascription_u32 e)"
    \<rightharpoonup> "CONST ascribeu32 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u64)"
    \<rightharpoonup> "CONST ascribeu64 0"
  "_shallow(_urust_numeral_ascription_1_u64)"
    \<rightharpoonup> "CONST ascribeu64 1"
  "_shallow(_urust_numeral_ascription_u64 e)"
    \<rightharpoonup> "CONST ascribeu64 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_usize)"
    \<rightharpoonup> "CONST ascribeu64 0"
  "_shallow(_urust_numeral_ascription_1_usize)"
    \<rightharpoonup> "CONST ascribeu64 1"
  "_shallow(_urust_numeral_ascription_usize e)"
    \<rightharpoonup> "CONST ascribeu64 (_Numeral e)"
  \<comment>\<open>Explicit scopes are relevant for initial parsing and can be removed when operating on ASTs\<close>
  "_shallow(_urust_scoping f)"
    \<rightharpoonup> "(_shallow f)"
  \<comment>\<open>The shallow embedding of standard if-then-else conditional\<close>
  "_shallow (_urust_if_then_else c t e)"
    \<rightharpoonup> "if (_shallow c) \<lbrace> (_shallow t) \<rbrace> else \<lbrace> (_shallow e) \<rbrace>"
  "_shallow (_urust_if_then c t)"
    \<rightharpoonup> "if (_shallow c) \<lbrace> (_shallow t) \<rbrace> else \<lbrace> (CONST skip) \<rbrace>"
  \<comment>\<open>Unsafe blocks are semantically meaningless and merely included to make \<^verbatim>\<open>\<mu>Rust\<close> look closer to
     upstream Rust code.\<close>
  "_shallow (_urust_unsafe_block t)"
    \<rightharpoonup> "_shallow t"

  "_shallow (_urust_funcall_with_args (_urust_callable_id id) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_identifier_as_function id) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_antiquotation emb) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args emb (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_fun_literal f) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow f) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_struct f id) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_identifier_as_function id) (_shallow (_urust_args_app f args))"

  \<comment>\<open>Turbofish with args\<close>
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_id id) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_fun_literal f) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow f) params) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_struct f id) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow (_urust_args_app f args))"

  "_shallow (_urust_args_app a bs)"
    \<rightharpoonup> "_urust_shallow_args_app (_shallow a) (_shallow bs)"
  "_shallow (_urust_args_single a)"
    \<rightharpoonup> "_urust_shallow_args_single (_shallow a)"
  "_shallow (_urust_funcall_no_args (_urust_callable_id id))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_identifier_as_function id)"
  "_shallow (_urust_funcall_no_args (_urust_callable_antiquotation emb))"
    \<rightharpoonup> "_urust_shallow_fun_no_args emb"
  "_shallow (_urust_funcall_no_args (_urust_callable_fun_literal f))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow f)"
  "_shallow (_urust_funcall_no_args (_urust_callable_struct f id))"
    \<rightharpoonup> "_shallow (_urust_funcall_with_args (_urust_callable_id id) (_urust_args_single f))"

  \<comment>\<open>Turbofish no args\<close>
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_id id) params))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_apply_params (_shallow_identifier_as_function id) params)"
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_fun_literal f) params))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_apply_params (_shallow f) params)"
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_struct f id) params))"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow (_urust_args_single f))"

  "_shallow (_urust_return_unit)"
    \<rightharpoonup> "_urust_shallow_return (CONST literal ())"
  "_shallow (_urust_return exp)"
    \<rightharpoonup> "_urust_shallow_return (_shallow exp)"
  "_shallow (_urust_bind_immutable pattern exp cont)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp) (_abs (_shallow_let_pattern pattern) (_shallow cont))"
  "_shallow (_urust_bind_immutable' pattern exp cont)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp) (_abs (_shallow_let_pattern pattern) (_shallow cont))"
  "_shallow_let_pattern (_urust_let_pattern_identifier id)"
    \<rightharpoonup> "_shallow_identifier_as_literal id"

  \<comment>\<open>Tuples\<close>
  "_shallow (_urust_tuple_args_double a b)"
    \<rightleftharpoons> "CONST tuple_base_pair (_shallow a) (_shallow b)"
  "_shallow (_urust_tuple_args_app a bs)"
    \<rightleftharpoons> "CONST tuple_cons (_shallow a) (_shallow bs)"
  "_shallow (_urust_tuple_constr args)"
    \<rightleftharpoons> "_shallow args"
  "_shallow (_urust_tuple_index_0 arg)"
    \<rightleftharpoons> "CONST tuple_index_0 (_shallow arg)"
  "_shallow (_urust_tuple_index_1 arg)"
    \<rightleftharpoons> "CONST tuple_index_1 (_shallow arg)"
  "_shallow (_urust_tuple_index_2 arg)"
    \<rightleftharpoons> "CONST tuple_index_2 (_shallow arg)"
  "_shallow (_urust_tuple_index_3 arg)"
    \<rightleftharpoons> "CONST tuple_index_3 (_shallow arg)"
  "_shallow (_urust_tuple_index_4 arg)"
    \<rightleftharpoons> "CONST tuple_index_4 (_shallow arg)"
  "_shallow (_urust_tuple_index_5 arg)"
    \<rightleftharpoons> "CONST tuple_index_5 (_shallow arg)"
  "_shallow_let_pattern (_urust_let_pattern_tuple args)"
    \<rightleftharpoons> "_shallow_let_pattern_args args"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_base_pair fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_pattern (_shallow_let_pattern snd_pat) (_idtdummy :: Tuple.tnil))"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_app fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_shallow_let_pattern_args snd_pat)"

  "_shallow (_urust_bind_mutable (_urust_identifier_hol_id var) exp cont)"
    \<rightharpoonup> "CONST bind (Ref::new \<langle>(_shallow exp)\<rangle>) (\<lambda>var. (_shallow cont))"
  "_shallow (_urust_sequence seqA seqB)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (_shallow seqB)"
  "_shallow (_urust_sequence_mono seqA)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (CONST skip)"

  "_shallow (_urust_identifier ident)"
    \<rightharpoonup> "CONST literal (_shallow_identifier_as_literal ident)"

  "_shallow (_urust_field_access exp fld)"
    \<rightharpoonup> "_urust_shallow_field_access (_shallow exp) (_shallow_identifier_as_field fld)"

  "_shallow (_urust_propagate exp)"
    \<rightharpoonup> "_urust_shallow_propagate (_shallow exp)"
  "_shallow (_urust_deref exp)"
    \<rightharpoonup> "_urust_shallow_store_dereference (_shallow exp)"

  "_shallow (_urust_assign lhs exp)"
    \<rightharpoonup> "_urust_shallow_store_update (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_word_assign_or lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_or (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_xor lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_xor (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_and lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_and (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_assign_add lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_add (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_closure_no_args exp)"
    \<rightharpoonup> "CONST literal (CONST FunctionBody (_shallow exp))"
  "_shallow (_urust_closure_with_args args exp)"
    \<rightharpoonup> "CONST literal (_shallow_abstract_args args exp)"

  "_shallow_abstract_args (_urust_formal_single (_urust_identifier_hol_id arg)) exp"
    \<rightharpoonup> "\<lambda>arg. CONST FunctionBody (_shallow exp)"
  "_shallow_abstract_args (_urust_formal_app (_urust_identifier_hol_id arg) args) exp"
    \<rightharpoonup> "\<lambda>arg. _shallow_abstract_args args exp"

  "_shallow_apply_params f (_urust_param_app p params)"
    \<rightharpoonup> "_shallow_apply_params (f p) params"
  "_shallow_apply_params f (_urust_param_single p)"
    \<rightharpoonup> "f p"

  (* Explicit translations for specific macro forms. More may be added as needed *)
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_ne) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_eq) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST panic (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST panic (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST panic (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST unimplemented (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST fatal (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST fatal (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST fatal (_string_token_to_hol str)"

 "_shallow (_urust_index exp idx)"
    \<rightharpoonup> "_urust_shallow_index (_shallow exp) (_shallow idx)"

  "_shallow (_urust_add x y)"
    \<rightharpoonup> "_urust_shallow_add (_shallow x) (_shallow y)"
  "_shallow (_urust_minus x y)"
    \<rightharpoonup> "_urust_shallow_minus (_shallow x) (_shallow y)"
  "_shallow (_urust_mul x y)"
    \<rightharpoonup> "_urust_shallow_mul (_shallow x) (_shallow y)"
  "_shallow (_urust_div x y)"
    \<rightharpoonup> "_urust_shallow_div (_shallow x) (_shallow y)"
  "_shallow (_urust_mod x y)"
    \<rightharpoonup> "_urust_shallow_mod (_shallow x) (_shallow y)"

  "_shallow (_urust_equality x y)"
    \<rightharpoonup> "_urust_shallow_equality (_shallow x) (_shallow y)"
  "_shallow (_urust_nonequality x y)"
    \<rightharpoonup> "_urust_shallow_nonequality (_shallow x) (_shallow y)"
  "_shallow (_urust_greater_equal x y)"
    \<rightharpoonup> "_urust_shallow_bool_ge (_shallow x) (_shallow y)"
  "_shallow (_urust_greater x y)"
    \<rightharpoonup> "_urust_shallow_bool_gt (_shallow x) (_shallow y)"
  "_shallow (_urust_less_equal x y)"
    \<rightharpoonup> "_urust_shallow_bool_le (_shallow x) (_shallow y)"
  "_shallow (_urust_less x y)"
    \<rightharpoonup> "_urust_shallow_bool_lt (_shallow x) (_shallow y)"

  "_shallow (_urust_bitwise_or x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_or (_shallow x) (_shallow y)"
  "_shallow (_urust_bitwise_and x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_and (_shallow x) (_shallow y)"
  "_shallow (_urust_bitwise_xor x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_xor (_shallow x) (_shallow y)"
  "_shallow (_urust_shift_left x y)"
    \<rightharpoonup> "_urust_shallow_word_shift_left (_shallow x) (_shallow y)"
  "_shallow (_urust_shift_right x y)"
    \<rightharpoonup> "_urust_shallow_word_shift_right (_shallow x) (_shallow y)"

  "_shallow (_urust_negation exp)"
    \<rightharpoonup> "_urust_shallow_negation (_shallow exp)"
  "_shallow (_urust_bool_conjunction x y)"
    \<rightharpoonup> "_urust_shallow_bool_conjunction (_shallow x) (_shallow y)"
  "_shallow (_urust_bool_disjunction x y)"
    \<rightharpoonup> "_urust_shallow_bool_disjunction (_shallow x) (_shallow y)"

  "_shallow( _urust_range x y)"
    \<rightharpoonup> "_urust_shallow_range (_shallow x) (_shallow y)"
  "_shallow( _urust_range_eq x y)"
    \<rightharpoonup> "_urust_shallow_range_eq (_shallow x) (_shallow y)"

  "_shallow (_urust_let_else ptrn exp el tail)"
    \<rightharpoonup> "_urust_shallow_let_else (_shallow_match_pattern ptrn) (_shallow exp) (_shallow el) (_shallow tail)"
  "_shallow (_urust_if_let ptrn exp this)"
    \<rightharpoonup> "_urust_shallow_if_let (_shallow_match_pattern ptrn) (_shallow exp) (_shallow this)"
  "_shallow (_urust_if_let_else ptrn exp this that )"
    \<rightharpoonup> "_urust_shallow_if_let_else (_shallow_match_pattern ptrn) (_shallow exp) (_shallow this) (_shallow that)"

  "_shallow (_urust_match exp branches)"
    \<rightharpoonup> "_urust_shallow_match (_shallow exp) (_shallow_match_branches branches)"

  "_shallow_match_branches (_urust_match1 pattern exp)"
    \<rightharpoonup> "_urust_shallow_match1 (_shallow_match_pattern pattern) (_shallow exp)"
  "_shallow_match_branches (_urust_match2 b0 b1)"
    \<rightharpoonup> "_urust_shallow_match2 (_shallow_match_branches b0) (_shallow_match_branches b1)"

  "_shallow_match_pattern _urust_match_pattern_other"
    \<rightharpoonup> "_urust_shallow_match_pattern_other"
  "_shallow_match_pattern (_urust_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_no_args (_shallow_identifier_as_literal id)"
  "_shallow_match_pattern (_urust_match_pattern_constr_with_args id args)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_with_args (_shallow_identifier_as_literal id) (_shallow_match_args args)"

  "_shallow_match_args (_urust_match_pattern_args_single arg)"
    \<rightharpoonup> "_urust_shallow_match_pattern_args_single (_shallow_match_arg arg)"
  "_shallow_match_args (_urust_match_pattern_args_app a bs)"
    \<rightharpoonup> "_urust_shallow_match_pattern_args_app (_shallow_match_arg a) (_shallow_match_args bs)"

  "_shallow_match_arg (_urust_match_pattern_arg_id id)"
    \<rightharpoonup> "_urust_shallow_match_pattern_arg_id id"
  "_shallow_match_arg _urust_match_pattern_arg_dummy"
    \<rightharpoonup> "_urust_shallow_match_pattern_arg_dummy"

  "_shallow (_urust_for_loop x iter body)"
    \<rightharpoonup> "_urust_shallow_for_loop (_shallow_let_pattern x) (_shallow iter) (_shallow body)"


abbreviation urust_constructor_some :: \<open>'a \<Rightarrow> ('s, 'a option, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_some \<equiv> lift_fun1 Some\<close>
abbreviation urust_constructor_ok :: \<open>'a \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_ok \<equiv> lift_fun1 Ok\<close>
abbreviation urust_constructor_err :: \<open>'e \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_err \<equiv> lift_fun1 Err\<close>

notation_nano_rust_function urust_constructor_some ("Some")
notation_nano_rust_function urust_constructor_ok   ("Ok")
notation_nano_rust_function urust_constructor_err  ("Err")

text\<open>By default, we map all identifiers to HOL through the identity function on their names.
We have to register this as a parse translation rather than a rule to give precedence to namings
registers via \<^text>\<open>notation_nano_rust\<close>, which use translation rules.\<close>

\<comment>\<open>NB: We could save some manual invocations of \<^text>\<open>notation_nano_rust\<close> if we changed the
default renaming convention here, and e.g. prepend all field names with \<^verbatim>\<open>field_lens_\<close>,
for example.\<close>
parse_translation\<open>[(\<^syntax_const>\<open>_urust_identifier_id\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_literal\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_function\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_field\<close>, K hd)]\<close>

subsection\<open>Tests\<close>

text \<open>TODO: Ultimately, I'd like to have custom commands to work with uRust expressions, but I
haven't yet figured out how to do this.\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>Bool_Type.true\<close>
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) {
    \<epsilon>\<open>\<up>0\<close>
  } else {
    \<epsilon>\<open>\<up>0\<close>
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  let (aa, bb, cc, dd, ee, ff, gg, hh) = tup;
  assert!(a == aa);
  assert!(b == bb);
  assert!(c == cc);
  assert!(d == dd);
  assert!(e == ee);
  assert!(f == ff);
  assert!(g == gg);
  assert!(h == hh);
  let tup2 = (a, (b, c));
  let (aaa, (bbb, ccc)) = tup2;
  assert!(aaa == a);
  assert!(bbb == b);
  assert!(ccc == c);
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = {
    assert!(True);
    assert!(False);
  };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) {
    Some(_) \<Rightarrow> (),
    _ \<Rightarrow> ()
  };
  if let Some(_) = Some(()) {
    ()
  };
  ()
\<rbrakk>\<close>

\<comment>\<open>TODO: Nested patterns not currently supported\<close>
value[simp]\<open>\<lbrakk>
  let one = \<llangle>1 :: 32 word\<rrangle>;
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  assert!((match Some(Some(None)) {
    Some(None) \<Rightarrow> one,
    _ \<Rightarrow> zero
  }) == zero)
\<rbrakk>\<close>

section\<open>Tuples\<close>
value[simp]\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((False, True), False)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), False)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), if False { (2 as u32, 3 as u32) } else { (4, 5) })
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>);
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3 == 3);
  assert!(tup.4 == 4);
  assert!(tup.5 == 5);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let tup = (a, b, c, (False, True));
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3.0 == False);
  assert!(tup.3.1 == True);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)
\<rbrakk>\<close>

(*
TODO: Fix this bug
lemma \<open>\<lbrakk>assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)\<rbrakk> = Expression (Success ())\<close>
  by simp
*)

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>;
  for i in lst {
    if (i.2.0) && i.2.1 {
      *x = i.0;
    } else {
      *x = i.1;
    }
  };
  x
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, nil), nil) # (1, 2, (True, False, nil), nil) # []\<rrangle>;
  for (a, b, (c, d)) in lst {
    if c && d {
      x += a;
    } else {
      x += b;
    }
  };
  x
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Ok(k) = Ok(()) else {
    return;
  };

  return k;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    return;
  } else {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    if True {
      return;
    } else {
      return;
    }
  } else {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) \<Rightarrow> { return; },
    None \<Rightarrow> { return; }
  };
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
   None \<Rightarrow> { return; },
   Some(y) \<Rightarrow> y
  };
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Err(e) = Ok(()) else {
    return True;
  };

  return e;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True || !True {
    {{{{{{{{{{
      42
    }}}}}}}}}}
  } else {
    0
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if !True {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let v = \<llangle>42 :: 64 word\<rrangle>;
  return v;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let (a,b) = (1,2);
  return;
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let (a,_) = (1,2);
  let (_,b) = (1,2);
  \<llangle>(a,b)\<rrangle>
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True {
    return True;
  } else {
    return True;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if \<llangle>True\<rrangle> {
    let v = 16;
    return v;
  } else {
    42
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  const FOO = 5;
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return 0;
  } else {
    return 2;
  }
\<rbrakk>\<close>

\<comment> \<open>Having a warning in the following test case is expected, see also RFC:
\<^url>\<open>https://rust-lang.github.io/rfcs/3137-let-else.html\<close>\<close>
term\<open>\<lbrakk>
  let x = if True { 0 } else { 1 };
  return x;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = (if True { 0 } else { 1 });
  return x;
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  let x = \<llangle>Some (0 :: nat)\<rrangle>;
  let Some(foo) = x else {
    assert!(False)
  };
  return;
\<rbrakk>)\<close>

term\<open>(FunctionBody \<lbrakk>
  {return;}; return;
\<rbrakk>)\<close>

definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>)\<close>
hide_const test

term\<open>(FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body\<close>

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
term\<open>\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression\<close>

term\<open>\<lbrakk>
  let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>);
  a + b + c
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let blub = 0;
  if let Some(x) = g(x) {
    return 0;
  } else {
    return 42;
  };
  return 12;
\<rbrakk>\<close>
end

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
  fixes h :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes i :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
begin

term\<open>\<lbrakk>
  h(a, b, c, a)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  i(a, b, c, a, b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  g(c);
  c.g();
\<rbrakk>\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>g\<close>(c);
  g(c);
  f(a,b);
  a.f(b);
  f(g(c),b);
  g(c).f(b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  f(g(c),b)
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x += b;
  *x
\<rbrakk>\<close>

end

\<comment> \<open>Equality/nonequality parsing tests\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
term \<open>\<lbrakk> m == n \<rbrakk>\<close>
term \<open>\<lbrakk> !(m == n) \<rbrakk>\<close>
term \<open>\<lbrakk> m != n \<rbrakk>\<close>
term \<open>\<lbrakk> m.h() \<rbrakk>\<close>
term \<open>\<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close>
term \<open>\<lbrakk> !x + y \<rbrakk>\<close>
term \<open>\<lbrakk> !(!x == x^y)  \<rbrakk>\<close>
end

\<comment> \<open>Range expression parse tests\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x..y \<rbrakk>\<close>
term \<open>\<lbrakk> x..=y \<rbrakk>\<close>
term \<open>\<lbrakk> for i in x .. y { () } \<rbrakk>\<close>
term \<open>\<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close>
end


\<comment> \<open>field access parsing tests\<close>

datatype_record testrec =
  field1 :: integer
  field2 :: bool
micro_rust_record testrec

datatype_record testrec2 =
  field3 :: testrec
  field4 :: \<open>bool option\<close>
micro_rust_record testrec2

context
  fixes x :: testrec
  fixes y :: testrec2
begin
term\<open> \<lbrakk> x \<rbrakk> \<close>
term \<open>\<lbrakk> x.field1 \<rbrakk>\<close>
term \<open>\<lbrakk> y.field4 \<rbrakk>\<close>
value \<open>\<lbrakk> y.field3.field1 \<rbrakk>\<close>
end

\<comment> \<open>Field access and assignment parsing tests\<close>

context
  fixes r :: \<open>('s, 'b, integer) ref\<close>
  fixes s :: \<open>('s, 'b, testrec2) ref\<close>
  fixes f :: \<open>('s, 'b, integer) ref \<Rightarrow> integer \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
begin

private definition dummy_dereference :: \<open>('s, 'b, 'v) ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference

term\<open>field4_lens\<close>
term \<open>\<lbrakk> r.f(10) \<rbrakk>\<close>
term\<open>bindlift2 focus_const (literal s) (literal field3_lens)\<close>
term \<open>\<lbrakk> *(s. field3_lens) \<rbrakk>\<close>
term\<open>store_dereference_const s\<close>
term \<open>\<lbrakk> (*s). field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = (*s).field3_lens.field1_lens \<rbrakk>\<close>
term \<open>\<lbrakk> r = *s.field3_lens.field1_lens \<rbrakk>\<close>

term \<open>\<lbrakk> r = 10 \<rbrakk>\<close>
term \<open>\<lbrakk> *(s.field4_lens) \<rbrakk>\<close>
term \<open>\<lbrakk> (*s).field4_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field1_lens = *r \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>

term \<open>\<lbrakk> s.field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field2_lens \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference
end

\<comment> \<open>unit value/unit return parsing tests\<close>
context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> () \<rbrakk>\<close>
term \<open>\<lbrakk> (); () \<rbrakk>\<close>
term \<open>\<lbrakk> (); (); \<rbrakk>\<close>
term \<open>\<lbrakk> return (); \<rbrakk>\<close>
term \<open>\<lbrakk> return; \<rbrakk>\<close>
term \<open>\<lbrakk> f(()) \<rbrakk>\<close>
term \<open>\<lbrakk> g((),True) \<rbrakk>\<close>
end

\<comment> \<open>closure parsing tests\<close>
context
  fixes f :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes h :: \<open>nat \<Rightarrow> (bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body) \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
  fixes n :: \<open>nat\<close>
begin
term \<open>\<lbrakk> || return x; \<rbrakk>\<close>
term \<open>\<lbrakk> |x| x \<rbrakk>\<close>
term \<open>\<lbrakk> |x, y| { let z = f(x,y); return z; }  \<rbrakk>\<close>
term \<open>\<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close>
end

\<comment> \<open>parameter parsing tests\<close>

context
  fixes f :: \<open>nat \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> f::<5>() \<rbrakk>\<close>
term \<open>\<lbrakk> g::<10>(True) \<rbrakk>\<close>
end

context
  fixes n :: \<open>nat option\<close>
  fixes m :: \<open>(bool,nat) result\<close>
begin
term \<open>\<lbrakk> let Some(x) = n else { return \<llangle>5\<rrangle>; }; return x; \<rbrakk>\<close>
end

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
term \<open>\<lbrakk> xs [0..100][42] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10][100] \<rbrakk>\<close>
end

parse_translation\<open>
let

\<comment>\<open>This is largely copied from \<^verbatim>\<open>HOL/Tools/String_Syntax.ML\<close> which defines a parse translation for
\<^text>\<open>_Literal ''foo''\<close> into \<^typ>\<open>char list\<close>. Unfortunately, parse translations don't seem to be
applied recursively, so instead of converting \<^text>\<open>_string_token_to_hol "foo"\<close> into
\<^text>\<open>_Literal ''foo''\<close>, we have to replicate the translation for \<^text>\<open>_Literal\<close> here.\<close>

fun mk_bit_syntax b =
  Syntax.const (if b = 1 then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>);

fun mk_bits_syntax len = map mk_bit_syntax o Integer.radicify 2 len;

fun plain_strings_of str =
  map fst (Lexicon.explode_string (str, Position.none));

fun ascii_ord_of c =
  if Symbol.is_ascii c then ord c
  else if c = "\<newline>" then 10
  else error ("Bad character: " ^ quote c);

fun mk_char_syntax i =
  list_comb (Syntax.const \<^const_syntax>\<open>Char\<close>, mk_bits_syntax 8 i);

fun mk_string_syntax [] = Syntax.const \<^const_syntax>\<open>Nil\<close>
  | mk_string_syntax (c :: cs) =
      Syntax.const \<^const_syntax>\<open>Cons\<close> $ mk_char_syntax (ascii_ord_of c)
        $ mk_string_syntax cs;

fun str_tok_to_hol ctxt [Free (str, _)] =
    (Syntax.const \<^const_syntax>\<open>String.implode\<close>) $ mk_string_syntax (plain_strings_of str)

in
  [(\<^syntax_const>\<open>_string_token_to_hol\<close>, str_tok_to_hol)]
end
\<close>

context
  fixes msg :: \<open>String.literal\<close>
    and b :: \<open>bool\<close>
    and o :: \<open>nat option\<close>
    and some_pa :: \<open>64 word\<close>
    and a_value :: \<open>32 word\<close>
    and a_code :: \<open>16 word\<close>
begin

term \<open>\<lbrakk> assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close>
term \<open>\<lbrakk> panic!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!(nm) \<rbrakk>\<close>

term\<open>\<lbrakk> a_value as u8\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u32\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close>

\<comment> \<open>Test string notation\<close>
term \<open>\<lbrakk> panic!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!("yikes!") \<rbrakk>\<close>

\<comment> \<open>Literally the same as the following\<close>
term \<open>\<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close>

\<comment> \<open>Test the logger\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close>

\<comment> \<open>Test unsafe blocks\<close>
term \<open>\<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close>

\<comment> \<open>Test ascription\<close>
term \<open>\<lbrakk> 0_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x4_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x12_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2000_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2f0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 1_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 0xffffffff0_usize \<rbrakk>\<close>

end

end
