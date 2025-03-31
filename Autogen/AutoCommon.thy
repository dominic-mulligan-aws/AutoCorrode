(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory AutoCommon
  imports Main
begin

ML\<open>
  \<comment>\<open>Trace level: The higher, the more verbose the logging gets\<close>
  val locality_trace_level = Attrib.setup_config_int @{binding "locality_trace_level"} (K 1)

  \<comment>\<open>Log text at given debug level; will be dropped if larger than \<^verbatim>\<open>locality_trace_level\<close>.\<close>
  fun locality_pretty_trace ctxt lvl =
    if lvl <= Config.get ctxt locality_trace_level then
      Pretty.string_of #> tracing
    else
      K ()

  \<comment>\<open>Lookup named theorem list by name. If it does not exist, return \<^verbatim>\<open>NONE\<close>.
     If it does, return the fully qualified name.\<close>
  fun named_theorems_check_opt (name : string) ctxt =
    Named_Theorems.check ctxt (name, Position.none) |> SOME
    handle ERROR _ => NONE
  
  \<comment>\<open>Lookup named theorem list by name. If it does not exist, create it.
  Return the triple of (a) a boolean indicating whether named theorem list was freshly
  created, (b) fully qualified name, (c) potentially updated context.\<close>
  fun check_create_named_theorems (name : string) ctxt =
    case named_theorems_check_opt name ctxt of
       NONE =>
         let
           val (name', ctxt') = Named_Theorems.declare (Binding.make (name, Position.none)) "" ctxt
           val _ = Pretty.text "Created named theorem list:" @ [Pretty.brk 1, Pretty.str name]
                |> Pretty.block |> locality_pretty_trace ctxt 1
         in
           (true, name', ctxt')
         end
     | SOME name' => (false, name', ctxt)

  fun prepare_rec_name (ctxt : Proof.context) (rec_name : string) =
    let
      (* Assumes a type of the form (_, _,..., _) ty and replaces the dummys with free type variables *)
      fun prepare_typ ty =
        let
          val (base, args) = Term.dest_Type ty
          val argnum = length args
          val tvars = Library.map_range (fn i => (TVar (("?'a", i), []))) argnum
        in
          Type (base, tvars)
        end
      val rec_ty = rec_name
        |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
        |> prepare_typ
      val (rec_name_full, _) = rec_ty |> dest_Type
    in
       (rec_ty, rec_name_full)
    end
\<close>

end