(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature CRUSH_DEBUG =
sig  
  val debug_simp_repetition: int Config.T

  (* Runs `simp` after stripping away the first N premises *)
  val debug_simp_strip_firstN: Proof.context -> int -> int -> tactic
  (* Runs `simp` after stripping away the N-th premises *)
  val debug_simp_strip_Nth: Proof.context -> int -> int -> tactic
  (* Repeatedly runs `simp` after stripping away the first k premises,
     with k running from 0 to N. Useful for debugging high simplifier
     runtimes when potentially caused by some specific premise(s). *)
  val debug_simp_strip_firstN': Proof.context -> int -> int -> tactic 
  (* Repeatedly runs `simp` after stripping away the k-th premise,
     with k running from 0 to N. Useful for debugging high simplifier
     runtimes when potentially caused by some specific premise(s). *)
  val debug_simp_strip_Nth': Proof.context -> int -> int -> tactic 
end;

structure Crush_Debug: CRUSH_DEBUG =
struct

  val debug_simp_repetition = Attrib.setup_config_int @{binding "debug_simp_repetition"} (K 5)
  
  fun repeat_N_times x n = 
    let fun core acc 0 = acc
          | core acc n = core (x :: acc) (n-1) in
      core [] n
    end

  val debug_simp_strip_firstN: Proof.context -> int -> int -> tactic = fn ctxt => fn N =>
    let val t = LOG' ctxt true (Int.toString N) (asm_full_simp_tac ctxt) THEN' (K no_tac) in
      thin_tac_idxs ctxt (range_of_nats N) 
        THEN' FIRST' (repeat_N_times t (Config.get ctxt debug_simp_repetition))
    end

  val debug_simp_strip_Nth: Proof.context -> int -> int -> tactic = fn ctxt => fn N =>
    let val t = LOG' ctxt true (Int.toString N) (asm_full_simp_tac ctxt) THEN' (K no_tac) in
      thin_tac_idx ctxt N THEN' FIRST' (repeat_N_times t (Config.get ctxt debug_simp_repetition))
    end

  val debug_simp_strip_firstN': Proof.context -> int -> int -> tactic = fn ctxt => fn N =>
    FIRST' (List.map (debug_simp_strip_firstN ctxt) (range_of_nats N))

  val debug_simp_strip_Nth': Proof.context -> int -> int -> tactic = fn ctxt => fn N =>
    FIRST' (List.map (debug_simp_strip_Nth ctxt) (range_of_nats N))

end;