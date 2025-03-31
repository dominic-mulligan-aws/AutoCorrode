(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust_Syntax
  imports Main
begin
(*>*)

section\<open>Micro Rust abstract syntax\<close>

text\<open>In this section, we introduce the abstract syntax of Micro Rust. We operate on a purely syntactic
level, extending Isabelle/HOL by a new syntactic category \<^text>\<open>urust\<close> for uRust programs that's separate from the syntactic
categories of HOL propositions, types and terms. Both the shallow and the deep embedding of Micro Rust into
HOL become syntax transformations \<^text>\<open>urust \<Rightarrow> logic\<close> from \<^text>\<open>urust\<close> into the category \<^text>\<open>logic\<close> of HOL terms.
Further, a Micro-Rust-to-Rust translation may be implemented in ML to automatically export Micro Rust to Rust.\<close>

subsection\<open>Syntax categories\<close>

text\<open>We introduce various syntax categories used in the specification of the grammar of Micro Rust.
The most important one is \<^text>\<open>urust\<close>, which is the category of all syntactically well-formed
Micro Rust expressions:\<close>

nonterminal urust

text\<open>An uninterpreted 'embedding' of Micro Rust into HOL which allows us to cast any Micro Rust parsing
problem as a term-parsing problem.\<close>

syntax
  "_urust_expression" :: \<open>urust \<Rightarrow> logic\<close> ("\<guillemotleft>_\<guillemotright>")

text\<open>The following is the syntax category of Micro Rust identifiers.\<close>

nonterminal urust_identifier

text\<open>Wildcard patterns:
Note: This wildcard cannot replace \<^verbatim>\<open>_urust_match_pattern_other\<close> as a match pattern.
But it will make the syntax ambiguous by allowing a wildcard match case to parse either as:
  \<^verbatim>\<open>"_urust_match_pattern_constr_no_args" ("_urust_identifier_wildcard")\<close>
or
  \<^verbatim>\<open>"_urust_match_pattern_other"\<close>.
We disambiguous this by making the wildcard identifier's precedence 999 instead\<close>
syntax
  "_urust_identifier_wildcard" :: \<open>urust_identifier\<close>
    ("'_" 999)
translations
  "_urust_identifier_wildcard"
  \<rightharpoonup> "_idtdummy"

text\<open>HOL identifiers can be used as Micro Rust identifiers:\<close>
syntax
  "_urust_identifier_id" :: \<open>id \<Rightarrow> urust_identifier\<close>
    ("_" [0]1000)

text\<open>The following are intermediate syntax categories required for the definition of \<^text>\<open>urust\<close>.\<close>
nonterminal urust_args \<comment>\<open>Comma-separated lists of uRust terms\<close>
nonterminal urust_formal_args \<comment> \<open>Comma-separated lists of uRust identifiers\<close>
nonterminal urust_params \<comment> \<open>Comma-separated lists of parameters (HOL terms)\<close>
nonterminal urust_callable
nonterminal urust_fun_literal
nonterminal urust_lhs
nonterminal urust_antiquotation
nonterminal urust_tuple_args

nonterminal urust_match_branch \<comment> \<open>A single branch of a match statement\<close>
nonterminal urust_match_branches \<comment> \<open>Comma-separate lists of match branches\<close>
nonterminal urust_match_pattern
nonterminal urust_match_pattern_arg
nonterminal urust_match_pattern_args

nonterminal urust_let_pattern
nonterminal urust_let_pattern_args

nonterminal urust_integral_type

subsection\<open>Core abstract syntax of \<^verbatim>\<open>\<mu>Rust\<close>\<close>

syntax
  \<comment>\<open>Identifiers (variable names) are valid \<^verbatim>\<open>\<mu>Rust\<close> terms\<close>
  "_urust_identifier" :: "urust_identifier \<Rightarrow> urust"
    ("_" [0]1000)
  "_urust_numeral" :: "num_const \<Rightarrow> urust"
    ("_" [0]1000)
  "_urust_numeral_0" :: "urust"
    ("0")
  "_urust_numeral_1" :: "urust"
    ("1")
  "_urust_u8" :: "urust_integral_type"
    ("u8")
  "_urust_u16" :: "urust_integral_type"
    ("u16")
  "_urust_u32" :: "urust_integral_type"
    ("u32")
  "_urust_u64" :: "urust_integral_type"
    ("u64")
  "_urust_usize" :: "urust_integral_type"
    ("usize")
  "_urust_parens" :: "urust \<Rightarrow> urust"
    ("'(_')" [0]999)
  "_urust_string_token" :: "string_token \<Rightarrow> urust"
    ("_")
  \<comment>\<open>Any HOL term can be explicitly lifted to \<^verbatim>\<open>\<mu>Rust\<close> as a literal\<close>
  "_urust_literal" :: "'value \<Rightarrow> urust"
    ("\<llangle>_\<rrangle>" [0]1000)
  "_urust_fun_literal1" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>1" [0]1000)
  "_urust_fun_literal2" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>2" [0]1000)
  "_urust_fun_literal3" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>3" [0]1000)
  "_urust_fun_literal4" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>4" [0]1000)
  "_urust_fun_literal5" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>5" [0]1000)
  "_urust_fun_literal6" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>6" [0]1000)
  "_urust_fun_literal7" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>7" [0]1000)
  "_urust_fun_literal8" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>8" [0]1000)
  "_urust_fun_literal9" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>9" [0]1000)
  "_urust_fun_literal10" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>1\<^sub>0" [0]1000)
  \<comment>\<open>Primitive casts\<close>
  "_urust_primitive_integral_cast_u8" :: "urust \<Rightarrow> urust"
    ("(_) as/ u8" [100]1000)
  "_urust_primitive_integral_cast_u16" :: "urust \<Rightarrow> urust"
    ("(_) as/ u16" [100]1000)
  "_urust_primitive_integral_cast_u32" :: "urust \<Rightarrow> urust"
    ("(_) as/ u32" [100]1000)
  "_urust_primitive_integral_cast_u64" :: "urust \<Rightarrow> urust"
    ("(_) as/ u64" [100]1000)
  "_urust_primitive_integral_cast_usize" :: "urust \<Rightarrow> urust"
    ("(_) as/ usize" [100]1000)
  "_urust_primitive_integral_cast_i32" :: "urust \<Rightarrow> urust"
    ("(_) as/ i32" [100]1000)
  "_urust_primitive_integral_cast_i64" :: "urust \<Rightarrow> urust"
    ("(_) as/ i64" [100]1000)
  \<comment>\<open>Integral literals at a given type\<close>
  "_urust_numeral_ascription_0_u8" :: "urust"
    ("0'_u8")
  "_urust_numeral_ascription_1_u8" :: "urust"
    ("1'_u8")
  "_urust_numeral_ascription_u8" :: "num_const \<Rightarrow> urust"
    ("_'_u8")
  "_urust_numeral_ascription_0_u16" :: "urust"
    ("0'_u16")
  "_urust_numeral_ascription_1_u16" :: "urust"
    ("1'_u16")
  "_urust_numeral_ascription_u16" :: "num_const \<Rightarrow> urust"
    ("_'_u16")
  "_urust_numeral_ascription_0_u32" :: "urust"
    ("0'_u32")
  "_urust_numeral_ascription_1_u32" :: "urust"
    ("1'_u32")
  "_urust_numeral_ascription_u32" :: "num_const \<Rightarrow> urust"
    ("_'_u32")
  "_urust_numeral_ascription_0_u64" :: "urust"
    ("0'_u64")
  "_urust_numeral_ascription_1_u64" :: "urust"
    ("1'_u64")
  "_urust_numeral_ascription_u64" :: "num_const \<Rightarrow> urust"
    ("_'_u64")
  "_urust_numeral_ascription_0_usize" :: "urust"
    ("0'_usize")
  "_urust_numeral_ascription_1_usize" :: "urust"
    ("1'_usize")
  "_urust_numeral_ascription_usize" :: "num_const \<Rightarrow> urust"
    ("_'_usize")
  \<comment> \<open>Breakpoints\<close>
  "_urust_pause" :: "urust" 
    ("\<y>\<i>\<e>\<l>\<d>")
  \<comment> \<open>Logging\<close>
  "_urust_log" :: "'value \<Rightarrow> 'value \<Rightarrow> urust" 
    ("\<l>\<o>\<g> \<llangle>_\<rrangle> \<llangle>_\<rrangle>")
  \<comment> \<open>The special unit value\<close>
  "_urust_unit" :: "urust"
    ("'(')")
  \<comment>\<open>Until 'abstract Micro Rust' is expressive enough, we might need to explicitly embed raw HOL expressions.\<close>
  "_urust_antiquotation" :: "'a \<Rightarrow> urust_antiquotation"
    ("\<epsilon>'\<open>//_'\<close>"[0]1000)
  "" :: \<open>urust_antiquotation \<Rightarrow> urust\<close> ("_")
  \<comment>\<open>Introducing an explicit scope within a Micro Rust program\<close>
  "_urust_scoping" :: "urust \<Rightarrow> urust"
    ("{/ _/ }"[0]1000)
  \<comment>\<open>Functions, closures, and macros\<close>
  "_urust_callable_id" :: "urust_identifier \<Rightarrow> urust_callable"
    ("_")
  "" :: "urust_antiquotation \<Rightarrow> urust_callable"
    ("_")
  "_urust_callable_fun_literal" :: "urust_fun_literal \<Rightarrow> urust_callable"
    ("_")
  "_urust_callable_struct" :: "urust \<Rightarrow> urust_identifier \<Rightarrow> urust_callable"
    ("_._" [999,1000]1000)
  "_urust_args_single" :: "urust \<Rightarrow> urust_args"
    ("_")
  "_urust_args_app" :: "urust \<Rightarrow> urust_args \<Rightarrow> urust_args"
    ("_,/ _")
  "_urust_macro_no_args" :: "urust_identifier \<Rightarrow> urust"
    ("_'!/ '(')" [1000]999)
  "_urust_macro_with_args" :: "urust_identifier \<Rightarrow> urust_args \<Rightarrow> urust"
    ("_'!/ '(_')" [1000,0]999)
  "_urust_funcall_with_args" :: "urust_callable \<Rightarrow> urust_args \<Rightarrow> urust"
    ("_/ '(_')"[1000,0]999)
  "_urust_funcall_no_args" :: "urust_callable \<Rightarrow> urust"
    ("_/ '(')"[1000]999)
  "_urust_param_single" :: "logic \<Rightarrow> urust_params"
    ("_")
  "_urust_param_app" :: "logic \<Rightarrow> urust_params \<Rightarrow> urust_params"
    ("_,/ _")
  "_urust_formal_single" :: "urust_identifier \<Rightarrow> urust_formal_args"
    ("_")
  "_urust_formal_app" :: "urust_identifier \<Rightarrow> urust_formal_args \<Rightarrow> urust_formal_args"
    ("_,/ _")
  "_urust_closure_with_args" :: "urust_formal_args \<Rightarrow> urust \<Rightarrow> urust"
    ("'|_'| _"[1000,20]10)
  "_urust_closure_no_args" :: "urust \<Rightarrow> urust"
    ("'|'| _"[20]10)
  "_urust_callable_with_params" :: "urust_callable \<Rightarrow> urust_params \<Rightarrow> urust_callable"
    ("_':':'<_'>" [1000,20]1000)
  \<comment>\<open>Tuples\<close>
  "_urust_tuple_args_double" :: "urust \<Rightarrow> urust \<Rightarrow> urust_tuple_args"
    ("_,/ _" [0,0]1000)
  "_urust_tuple_args_app" :: "urust \<Rightarrow> urust_tuple_args \<Rightarrow> urust_tuple_args"
    ("_,/ _" [0,1000]1000)
  "_urust_tuple_constr" :: "urust_tuple_args \<Rightarrow> urust"
    ("'(_')" [1000]998)
  "_urust_tuple_index_0" :: "urust \<Rightarrow> urust"
    ("_'.0" [998]998)
  "_urust_tuple_index_1" :: "urust \<Rightarrow> urust"
    ("_'.1" [998]998)
  "_urust_tuple_index_2" :: "urust \<Rightarrow> urust"
    ("_'.2" [998]998)
  "_urust_tuple_index_3" :: "urust \<Rightarrow> urust"
    ("_'.3" [998]998)
  "_urust_tuple_index_4" :: "urust \<Rightarrow> urust"
    ("_'.4" [998]998)
  "_urust_tuple_index_5" :: "urust \<Rightarrow> urust"
    ("_'.5" [998]998)
  \<comment>\<open>We have very basic support for let-patterns: identifiers and tuple destruction\<close>
  "_urust_let_pattern_identifier" :: "urust_identifier \<Rightarrow> urust_let_pattern"
    ("_")
  "_urust_let_pattern_tuple" :: "urust_let_pattern_args \<Rightarrow> urust_let_pattern"
    ("'(_')")
  "_urust_let_pattern_tuple_base_pair" :: "urust_let_pattern \<Rightarrow> urust_let_pattern \<Rightarrow> urust_let_pattern_args"
    ("_, _")
  "_urust_let_pattern_tuple_app" :: "urust_let_pattern \<Rightarrow> urust_let_pattern_args \<Rightarrow> urust_let_pattern_args"
    ("(_), (_)")
  \<comment>\<open>The monadic composition of two Micro Rust programs, ignoring the result of the first\<close>
  "_urust_sequence" :: "urust \<Rightarrow> urust \<Rightarrow> urust"
    ("_;_" [11,10]10)
  "_urust_sequence_mono" :: "urust \<Rightarrow> urust"
    ("_;" [11]10)
  \<comment>\<open>Add immutable binding\<close>
  "_urust_bind_immutable" :: "urust_let_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("let/ _/ =/ _;// _" [1000,20,10]10)
  "_urust_bind_immutable'" :: "urust_let_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("const/ _/ =/ _;// _" [1000,20,10]10)
  \<comment>\<open>Add mutable binding\<close>
  "_urust_bind_mutable" :: "urust_identifier \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("let/ mut/ _/ =/ _;// _" [1000,20,10]10)
  \<comment>\<open>Standard if-then-else conditional\<close>
  "_urust_if_then_else" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else/ {/ _/ }"[20,0,0]21)
  \<comment>\<open>Standard if-then conditional\<close>
  "_urust_if_then" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }"[20,0]20)
  "_urust_return" :: \<open>urust \<Rightarrow> urust\<close>
    ("return _;")
  "_urust_return_unit" :: \<open>urust\<close>
    ("return/ ;")
  \<comment>\<open>Unsafe\<close>
  "_urust_unsafe_block" :: \<open>urust \<Rightarrow> urust\<close>
    ("unsafe/ {/ _ /}")
  \<comment>\<open>Indexing and accessing\<close>
  "_urust_field_access" :: \<open>urust \<Rightarrow> urust_identifier \<Rightarrow> urust\<close>
    ("_._" [99,1000]100)
  "_urust_index" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("_/ '[_']" [100,0]100)

  \<comment>\<open>Other control flow constructs.  TODO: \<^verbatim>\<open>for\<close> loops should accept patterns?\<close>
  "_urust_for_loop"
    :: \<open>urust_let_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("for _ in (_) {/ _/ }" [100,20,0]11)

  "_urust_let_else" :: \<open>urust_match_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("let _ = (_) else { (_) } ; (_)" [100,20,0,10]10)

  "_urust_if_let" :: \<open>urust_match_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) }" [100,20,0]11)

  "_urust_if_let_else" :: \<open>urust_match_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) } else { (_) }" [100,20,0,0]11)

  "_urust_match"  :: "[urust, urust_match_branches] \<Rightarrow> urust"  ("match (_) {/ _/ }" [20, 10]20)
  "_urust_match1" :: "[urust_match_pattern, urust] \<Rightarrow> urust_match_branches"  ("(2_ \<Rightarrow>/ _)" [100, 20] 21)
  "_urust_match2" :: "[urust_match_branches, urust_match_branches] \<Rightarrow> urust_match_branches"  ("_/, _" [21, 20]20)

  \<comment>\<open>Basic case patterns, restricted to constructor identifiers followed by a potentially empty list of argument identifiers\<close>
  "_urust_match_pattern_other" :: \<open>urust_match_pattern\<close>
    ("'_")
  "_urust_match_pattern_constr_no_args" :: \<open>urust_identifier \<Rightarrow> urust_match_pattern\<close>
    ("_" [1000]100)
  "_urust_match_pattern_constr_with_args" :: \<open>urust_identifier \<Rightarrow> urust_match_pattern_args \<Rightarrow> urust_match_pattern\<close>
    ("_ '(_')"[1000,100]100)
  "_urust_match_pattern_arg_id" :: \<open>id \<Rightarrow> urust_match_pattern_arg\<close>
    ("_")
  "_urust_match_pattern_arg_dummy" :: \<open>urust_match_pattern_arg\<close>
    ("'_")
  "_urust_match_pattern_args_single" :: \<open>urust_match_pattern_arg \<Rightarrow> urust_match_pattern_args\<close>
    ("_")
  "_urust_match_pattern_args_app" :: \<open>urust_match_pattern_arg \<Rightarrow> urust_match_pattern_args \<Rightarrow> urust_match_pattern_args\<close>
    ("_,/ _"[1000,100]100)

  \<comment> \<open>See the rust documentation for a list of expression precedences and fixities:
       https://doc.rust-lang.org/reference/expressions.html\<close>

  "_urust_propagate" :: \<open>urust \<Rightarrow> urust\<close>
    ("_'?" [400]400)

  "_urust_negation" :: \<open>urust \<Rightarrow> urust\<close>
    ("!_" [301]300)
  "_urust_deref" :: \<open>urust \<Rightarrow> urust\<close>
    ("*_" [200]100)

  \<comment>\<open>Arithmetic expressions\<close>
  "_urust_mul" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "*" 50)
  "_urust_div" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "'/" 50)
  "_urust_mod" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "%" 50)

  "_urust_add" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "+" 49)
  "_urust_minus" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "-" 49)

  "_urust_shift_right" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl ">>" 48)
  "_urust_shift_left" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "<<" 48)

  "_urust_bitwise_and" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "&" 47)
  "_urust_bitwise_xor" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "^" 46)
  "_urust_bitwise_or" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "|" 45)

  "_urust_equality" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "==" 44)
  "_urust_nonequality" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "!=" 44)

  \<comment>\<open>Comparison\<close>
  "_urust_greater_equal" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix ">=" 44)
  "_urust_less_equal" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "<=" 44)
  "_urust_greater" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix ">" 44)
  "_urust_less" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "<" 44)

  "_urust_bool_conjunction" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl \<open>&&\<close> 43)

  "_urust_bool_disjunction" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl \<open>||\<close> 42)

  "_urust_range" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix \<open>..\<close> 41)
  "_urust_range_eq" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix \<open>..=\<close> 41)

  "_urust_assign" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixr "=" 40)

  "_urust_assign_add"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "+=" 40)
  "_urust_assign_minus"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "-=" 40)
  "_urust_assign_mul"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "*=" 40)
  "_urust_assign_mod"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "%=" 40)
  "_urust_word_assign_and"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "&=" 40)
  "_urust_word_assign_or"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "|=" 40)
  "_urust_word_assign_xor"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "^=" 40)
  "_urust_word_assign_shift_left"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "<<=" 40)
  "_urust_word_assign_shift_right"
     :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr ">>=" 40)

subsection\<open>Breaking long identifiers\<close>

text\<open>Expressions of the form \<^verbatim>\<open>foo.bar\<close> are parsed by Isabelle's inner syntax parser
as single tokens of syntactic type \<^text>\<open>longid\<close>, which doesn't match the Rust meaning as a
call to a structure method.

We temporarily interpret \<^text>\<open>longid\<close> as atomic callables to get through the parsing stage, and
then use a manual parse AST translation to break the \<^text>\<open>longid\<close> into its parts and reinterpret
calls as structure method calls.\<close>

nonterminal urust_temporary_long_identifier
syntax
  \<comment>\<open>Mark those as temporary to indicate that semantics definitions need not deal with it.
It is immediately removed after parsing.\<close>
  "_urust_temporary_long_id" :: \<open>longid \<Rightarrow> urust_temporary_long_identifier\<close>
    ("_" [0]1000)

  \<comment>\<open>Allow long ids in a few grammar productions normally taking ordinary identifiers\<close>
  "_urust_temporary_callable_id_long" :: \<open>urust_temporary_long_identifier \<Rightarrow> urust_callable\<close>
    ("_" [0]1000)
  "_urust_temporary_callable_struct_long" :: "urust \<Rightarrow> urust_temporary_long_identifier \<Rightarrow> urust_callable"
    ("_._" [999,1000]1000)
  "_urust_temporary_field_access_long" :: \<open>urust \<Rightarrow> urust_temporary_long_identifier \<Rightarrow> urust\<close>
    ("_._" [99,1000]100)
  "_urust_temporary_identifier_long" :: \<open>urust_temporary_long_identifier \<Rightarrow> urust\<close>
    ("_" [0]1000)

text\<open>First, we register a parse AST translation splitting long IDs at dots (".") and emitting them
as an anonymous \<^ML>\<open>Ast.Appl\<close>, with one \<^text>\<open>urust_identifier\<close> argument per component.\<close>
parse_ast_translation\<open>
let
  fun split_at_dots str = let
     val scan_to_dot = (Scan.repeat (Scan.unless ($$ ".") (Scan.one Symbol.not_eof)))
     val skip_over_dot = ($$ ".") || Scan.succeed ""
     val extract_part = (scan_to_dot --| skip_over_dot) >> implode
     val splitter = Scan.finite Symbol.stopper
             (Scan.repeat (Scan.unless (Scan.one Symbol.is_eof) extract_part)) in
     fst (splitter (Symbol.explode str))
   end
  \<comment>\<open>ML representations of the relevant Nano Rust grammar productions\<close>
  fun ast_urust_identifier_id str =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_identifier_id\<close>) [Ast.Variable str]
  fun ast_urust_identifier ast =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_identifier\<close>) [ast]
  fun ast_urust_field_access func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_field_access\<close>) [obj, func]
  \<comment>\<open>This does currently only work for long identifiers of the form \<^text>\<open>id.id\<close>.\<close>
  fun break_long_identifier [long_id] =
     let val parts = long_id |> Ast.pretty_ast |> Pretty.string_of |> split_at_dots
         val parts_as_ids = map (ast_urust_identifier_id) parts
     in Ast.Appl parts_as_ids end
in
  [(\<^syntax_const>\<open>_urust_temporary_long_id\<close>, K break_long_identifier)]
end
\<close>

text\<open>Next, we go through all temporary grammar productions using long IDs and adjust them according to the
intended meaning of the "." operator in the respective context. For example, where a long identifier is used
as a standalone uRust term, dots are field projections. In contrast, if a long identifier is used as a callable,
it should be converted into a method invocation.

Note that since parse AST translations are called bottom-up, by the time the parse AST translations below
are called, long IDs have already been converted into anynomous AST applications, which gives us easy
access to the components of the long ID.\<close>
parse_ast_translation\<open>
let
  fun debug_result str res =
     (* writeln ("parse AST translation for temporary long " ^ str ^ ", result "
              ^ (Pretty.string_of (Ast.pretty_ast res))) *)
     ()
  fun ast_urust_identifier ast =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_identifier\<close>) [ast]
  fun ast_urust_field_access func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_field_access\<close>) [obj, func]
  fun ast_urust_callable_struct func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_callable_struct\<close>) [obj, func]

  fun convert_temporary_identifier_long [Ast.Appl (head :: projections)] =
     let val head = ast_urust_identifier head
         val res = fold ast_urust_field_access projections head
         val _ = debug_result "ID" res
     in res end

  fun convert_temporary_callable_id_long [Ast.Appl (head :: projections)] =
     let val head = ast_urust_identifier head
         val (body, method) = split_last projections
         val obj = fold ast_urust_field_access body head
         val res = ast_urust_callable_struct method obj
         val _ = debug_result "callable id" res
     in res end

  fun convert_temporary_callable_struct_long [head, Ast.Appl projections] =
     let val (body, method) = split_last projections
         val obj = fold ast_urust_field_access body head
         val res = ast_urust_callable_struct method obj
         val _ = debug_result "callable struct" res
     in res end

  fun convert_temporary_field_access_long [head, Ast.Appl projections] =
     let val res = fold ast_urust_field_access projections head
         val _ = debug_result "field access" res
     in res end
in
  [(\<^syntax_const>\<open>_urust_temporary_identifier_long\<close>,      K convert_temporary_identifier_long),
   (\<^syntax_const>\<open>_urust_temporary_callable_id_long\<close>,     K convert_temporary_callable_id_long),
   (\<^syntax_const>\<open>_urust_temporary_callable_struct_long\<close>, K convert_temporary_callable_struct_long),
   (\<^syntax_const>\<open>_urust_temporary_field_access_long\<close>,    K convert_temporary_field_access_long) ]
end
\<close>

(*<*)
end
(*>*)
