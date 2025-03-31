(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Various parsers needed for tacticals and `crush` arguments. *)

signature PARSERS = 
sig
  (* parse an ML expression of type `Proof.context -> int -> tactic` *)
  val parse_tactic: (Proof.context -> int -> tactic) parser
  (* parse an ML expression of type `Proof.context -> term -> bool` *)
  val parse_term_filter: (Proof.context -> term -> bool) parser
  (* parse a (context-dependent) method; also return string description *)
  val parse_method_with_name : (string * (Proof.context -> Method.method)) parser
  (* parse a (context-dependent) method *)
  val parse_method : (Proof.context -> Method.method) parser
  (* parse goal filter pattern -- takes the entire goal as input *)
  val parse_goal_filter_pattern : (Proof.context -> term -> bool) parser
  (* parse premise filter pattern -- takes the entire goal as input *)
  val parse_premise_filter_pattern : (Proof.context -> term -> bool) parser
  (* parse "true" or "false" as bool *)
  val parse_bool : bool parser

end

(* Signature for parsers of ML expressions of a given type *)
signature ML_PARSER = 
sig
  type T
  (* parse an ML expression as a value of the target type *)
  val ml_parse: T parser
  (* morally private, but has to be exposed to make the implementation work -- don't use this *)
  val set_data: T -> Context.generic -> Context.generic
end

(* Construction of ML-parsers

  While we may have missed a more general parsing functionality in the 
  distribution, there is an ML self-evaluation routine for expressions of type 
  `Generic.context -> Generic.context`, by means of `ML_Context.expression`.

  We extend this functionality to evaluation of expressions of other types, as follows:

  1/ Use the `Generic_Data` mechanism to add context state of the desired type.

  2/ We wrap the expression to be parsed into a context-transformer expression which sets the newly 
  introduced context field. This is happening at the syntactic level / the 'inner' ML.

  3/ Evaluate this ML expression to get an honest context transformer in the 'outer' ML.

  4/ One applies this transformer to the current context, and then reads the new field.

  All together, this gives a function `context -> Input.source -> target_type` as desired. 
*)

(* Arguments:

  - T: target type of the parser
  - name: Name that the value of the functor will be given to.

  That is, you _must_ write 

  ```ML
  struct {NAME} = MLParser(struct 
    type T = {TYPE}
    val name = "{NAME}"
  )
  ```

  otherwise the ML-in-ML evaluation mechanism will not work. 
*)

functor MLParser (Target: sig type T val name: string end) : ML_PARSER =
struct
  type T = Target.T

  structure Data = Generic_Data (
   type T = { tmp_data: T option };
   val empty : T = { tmp_data = NONE };
   fun merge ({tmp_data=g0, ...},{tmp_data=g1, ...}) : T = { tmp_data = merge_options (g0,g1) })

  val get_tmp_data = Data.get #> #tmp_data;
  fun set_data g = g |> SOME |> (fn v => fn {tmp_data=_} => {tmp_data = v }) |> Data.map

  fun the_tmp_data context = case get_tmp_data context of
    SOME g => g | NONE => raise Fail "Temporary data unset";

  (* Here's where the magic happens: Wrap input ML expression into a context transformer
     modifying the context field created above, apply the resulting ML to the given context,
     and extract the field afterwards. Because this is evaluated at the caller, we have to
     know the name of the concrete instantiation of the functor. *)
  val ml_parse : T parser =
    Parse.ML_source >> (fn source => 
      let val src = ML_Lex.read_source source in
      ML_Context.expression (Input.pos_of source)
        (ML_Lex.read ("Context.>> (" ^ Target.name ^ ".set_data (") @ src @ ML_Lex.read "))")
        (Context.the_generic_context ())
      |> the_tmp_data end)
end

(* Parser for ML expressions of type `Proof.context -> int -> tactic` *)
structure TacticParser = MLParser(struct 
  type T = Proof.context -> int -> tactic 
  val name="TacticParser" 
end)

(* Parser for ML expressions of type `Proof.context -> term -> bool` *)
structure TermFilterParser = MLParser(struct
  type T = Proof.context -> term -> bool
  val name ="TermFilterParser"
end)

structure Parser: PARSERS =
struct

  val parse_term_filter = TermFilterParser.ml_parse
  val parse_tactic = TacticParser.ml_parse

  val parse_method_with_name  = Parse.embedded_input >> 
    (fn src => (Input.string_of src, fn ctxt =>
      Method.evaluate (Method.read_closure_input ctxt src |> fst) ctxt ))

  val parse_method = parse_method_with_name >> snd

  val parse_goal_filter_pattern : (Proof.context -> term -> bool) parser =
    Parse.string >> metagoal_satisfies_pattern

  val parse_premise_filter_pattern : (Proof.context -> term -> bool) parser =
    Parse.string >> premise_satisfies_pattern

  val parse_bool : bool parser = (Args.$$$ "true" >> K true) || (Args.$$$ "false" >> K false)

end
