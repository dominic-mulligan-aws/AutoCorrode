(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Undefined
  imports Main
begin
(*>*)

section\<open>Various types of undefinedness\<close>

text\<open>HOL provides the \<^verbatim>\<open>undefined\<close> constant which inhabits every type and can be used in a similar
way to \<^verbatim>\<open>assert false\<close> in OCaml (in fact, in OCaml it is basically extracted to exactly that by the
code generator).  Unfortunately, this means that \<^verbatim>\<open>undefined\<close> is used for a variety of different
things:

\begin{itemize*}
\item
Legitimate cases of undefined behaviour, for example the output of a partial function at an input
outside that function's domain,
\item
Unimplemented functionality which will at some point become implemented,
\item
Code paths through a function that should be impossible to hit owing to some global invariant, or
a precondition on the function's inputs.  In a dependently-typed system like Coq or Agda we could
try to use the type-system to rule these sorts of cases out, but in HOL we simply make the function
undefined at that point.
\end{itemize*}

This file therefore introduces a few new abbreviations for \<^verbatim>\<open>undefined\<close> which will allow us to
distinguish between these different usages of the constant in a more declarative manner.

First, we have \<^verbatim>\<open>unimplemented\<close>, which captures the idea that some functionality is simply not
implemented yet:\<close>
abbreviation unimplemented :: \<open>'a\<close> where
  \<open>unimplemented \<equiv> undefined\<close>

text\<open>Next, \<^verbatim>\<open>impossible\<close> expresses that fact that as code path is impossible to hit.  A given reason
in the form of a string literal is provided:\<close>
abbreviation impossible :: \<open>String.literal \<Rightarrow> 'a\<close> where
  \<open>impossible _ \<equiv> undefined\<close>

text\<open>Lastly, we continue to use \<^verbatim>\<open>undefined\<close> for legitimate cases of undefinedness.\<close>

(*<*)
end
(*>*)