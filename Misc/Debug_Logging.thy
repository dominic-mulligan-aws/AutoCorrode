(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Debug_Logging
  imports "HOL-Library.Word"
begin
(*>*)

section\<open>Debug logging for tracing Micro Rust execution\<close>

subsection\<open>Log data\<close>

text\<open>This, and the following \<^verbatim>\<open>log_data\<close> type, are types used for logging from \<^verbatim>\<open>\<mu>Rust\<close> code,
somewhat akin to a format string in Rust.\<close>
datatype log_entry
  = LogWord   \<open>nat\<close> \<open>nat\<close> \<comment> \<open>First value is the machine word length, next its value\<close>
  | LogNat    \<open>nat\<close>
  | LogBool   \<open>bool\<close>
  | LogString \<open>String.literal\<close>

text\<open>Log data is just a list of \<^verbatim>\<open>log_entry\<close> records:\<close>
type_synonym log_data = \<open>log_entry list\<close>

subsection\<open>The \<^verbatim>\<open>Debug\<close> typeclass\<close>

text\<open>This is an analogue of the Rust \<^verbatim>\<open>Debug\<close> trait which we use for spitting out debug
representations of values for use in \<^verbatim>\<open>\<mu>Rust\<close> logging and similar.\<close>
class generate_debug =
  fixes
    \<comment> \<open>Produce a \<^verbatim>\<open>log_data\<close> representation of the value.  Note that we use \<^verbatim>\<open>log_data\<close> rather than
        \<^verbatim>\<open>char list\<close> or \<^verbatim>\<open>String.literal\<close> here as that defers decisions over how numeric types, for
        example, should be printed to the environment (read: \<^verbatim>\<open>OCaml\<close> logging framework).\<close>
    generate_debug :: \<open>'a \<Rightarrow> log_data\<close>

subsection\<open>Utility functions\<close>

text\<open>Utility function to promote character lists to \<^verbatim>\<open>log_entry\<close>:\<close>
definition str :: \<open>char list \<Rightarrow> log_entry\<close> where
  \<open>str \<equiv> LogString \<circ> String.implode\<close>

fun intersperse :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>intersperse sep []     = []\<close> |
  \<open>intersperse sep [x]    = [x]\<close> |
  \<open>intersperse sep (x#xs) = x#sep#intersperse sep xs\<close>

text\<open>Renders a debug output for a value of a Rust structural type.\<close>
definition struct :: \<open>char list \<Rightarrow> (char list \<times> log_data) list \<Rightarrow> log_data\<close> where
  \<open>struct n fields \<equiv>
     let header  = [str n, str '' { ''] in
     let clauses = [(str fname) # str '': '' # f. (fname, f) \<leftarrow> fields] in
     let body    = intersperse [str '', ''] clauses in
     let closing = [str '' }''] in
       header @ concat body @ closing\<close>

subsection\<open>Common \<^verbatim>\<open>Debug\<close> typeclass instantiations\<close>

text\<open>Some standard instances:\<close>
instantiation nat :: generate_debug
begin

definition generate_debug_nat where
  \<open>generate_debug_nat n \<equiv> [LogNat n]\<close>

instance ..

end

instantiation bool :: generate_debug
begin

definition generate_debug_bool where
  \<open>generate_debug_bool n \<equiv> [LogBool n]\<close>

instance ..

end

instantiation String.literal :: generate_debug
begin

definition generate_debug_literal where
  \<open>generate_debug_literal n \<equiv> [LogString n]\<close>

instance ..

end

instantiation unit :: generate_debug
begin

definition generate_debug_unit :: \<open>unit \<Rightarrow> log_data\<close> where
  \<open>generate_debug_unit _ \<equiv> [str ''()'']\<close>

instance ..

end

instantiation prod :: (generate_debug, generate_debug)generate_debug
begin

definition generate_debug_prod :: \<open>'a \<times> 'b \<Rightarrow> log_data\<close> where
  \<open>generate_debug_prod p \<equiv>
     str ''(''#generate_debug (fst p)@(str '', ''#generate_debug (snd p)@[str '')''])\<close>

instance ..

end

instantiation word :: (len)generate_debug
begin

definition generate_debug_word :: \<open>'a::{len} word \<Rightarrow> log_data\<close> where
  \<open>generate_debug_word w \<equiv> [LogWord (LENGTH('a)) (unat w)]\<close>

instance ..

end

instantiation list :: (generate_debug)generate_debug
begin

definition generate_debug_list :: \<open>'a list \<Rightarrow> log_data\<close> where
  \<open>generate_debug_list xs \<equiv>
     let components = List.map generate_debug xs in
     let body       = intersperse [str '', ''] components in
       str ''[''#concat body@[str '']'']\<close>

instance ..

end

(*<*)
end
(*>*)