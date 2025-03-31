(* arith.ML

  Some basic material about nat and word (in)equalities *)

signature CRUSH_ARITH =
sig  

  val is_nat_eq : term -> bool
  val is_nat_ineq : term -> bool
  val is_word_eq : term -> bool
  val is_word_ineq : term -> bool
  val is_nat_or_word_lt : term -> bool
  val is_nat_or_word_le : term -> bool

  val is_arithmetic_premise : term -> bool

  val filter_arithmetic_premises_tac : Proof.context -> int -> tactic
  val ltac_core : Proof.context -> int -> tactic
  val ltac : Proof.context -> bool -> int -> tactic
  val ltac_full : Proof.context -> int -> tactic
end

structure Crush_Arith : CRUSH_ARITH = 
struct
  val is_nat_eq : term -> bool =
     head_of #> curry (op =) @{term \<open>HOL.eq :: nat \<Rightarrow> nat \<Rightarrow> bool\<close>}

  val is_nat_ineq : term -> bool =
     head_of #> curry (op =) @{term \<open>HOL.not_equal:: nat \<Rightarrow> nat \<Rightarrow> bool\<close>}

  val is_word_eq : term -> bool = fn t =>
     head_of t = @{term \<open>HOL.eq :: ( 8 word) \<Rightarrow> ( 8 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.eq :: (16 word) \<Rightarrow> (16 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.eq :: (32 word) \<Rightarrow> (32 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.eq :: (64 word) \<Rightarrow> (64 word) \<Rightarrow> bool\<close>}

  val is_word_ineq : term -> bool = fn t =>
     head_of t = @{term \<open>HOL.not_equal :: ( 8 word) \<Rightarrow> ( 8 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.not_equal :: (16 word) \<Rightarrow> (16 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.not_equal :: (32 word) \<Rightarrow> (32 word) \<Rightarrow> bool\<close>}    orelse
     head_of t = @{term \<open>HOL.not_equal :: (64 word) \<Rightarrow> (64 word) \<Rightarrow> bool\<close>}

  fun is_nat_or_word_lt (Const (@{const_name Orderings.ord_class.less}, @{typ \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>}) $ _ $ _) = true
    | is_nat_or_word_lt (Const (@{const_name Orderings.ord_class.less}, @{typ \<open> 8 word \<Rightarrow>  8 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_lt (Const (@{const_name Orderings.ord_class.less}, @{typ \<open>16 word \<Rightarrow> 16 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_lt (Const (@{const_name Orderings.ord_class.less}, @{typ \<open>32 word \<Rightarrow> 32 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_lt (Const (@{const_name Orderings.ord_class.less}, @{typ \<open>64 word \<Rightarrow> 64 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_lt _ = false

  fun is_nat_or_word_le (Const (@{const_name Orderings.ord_class.less_eq}, @{typ \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>}) $ _ $ _) = true
    | is_nat_or_word_le (Const (@{const_name Orderings.ord_class.less_eq}, @{typ \<open> 8 word \<Rightarrow>  8 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_le (Const (@{const_name Orderings.ord_class.less_eq}, @{typ \<open>16 word \<Rightarrow> 16 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_le (Const (@{const_name Orderings.ord_class.less_eq}, @{typ \<open>32 word \<Rightarrow> 32 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_le (Const (@{const_name Orderings.ord_class.less_eq}, @{typ \<open>64 word \<Rightarrow> 64 word \<Rightarrow> bool\<close>} ) $ _ $ _) = true
    | is_nat_or_word_le _ = false

  val is_arithmetic_premise : term -> bool = fn t =>
     let val t = find_conclusion t in
         is_nat_eq t orelse is_nat_ineq t orelse is_word_eq t orelse is_word_ineq t orelse
         is_nat_or_word_lt t orelse is_nat_or_word_le t
     end

  val filter_arithmetic_premises_tac : Proof.context -> int -> tactic = fn ctxt =>
     DETERM o (filter_prems_tac ctxt is_arithmetic_premise)

  val ltac_defs_tac : Proof.context -> int -> tactic = fn ctxt =>
     let val crush_constants = Named_Theorems.get ctxt @{named_theorems crush_constants} in
       safe_simp_only_tac ctxt crush_constants
     end

  val ltac_intros_tac : Proof.context -> int -> tactic =
     intro_tac @{thms word_nat_intros word_nat_intros_weak}

  val ltac_simps_tac : Proof.context -> int -> tactic = fn ctxt =>
     safe_simp_only_tac ctxt @{thms word_nat_simps}

  val ltac_elims_tac : Proof.context -> int -> tactic =
     elim_tac @{thms word_nat_elims}

  val ltac_subst_simps_asm_tac : Proof.context -> int -> tactic = fn ctxt =>
     EqSubst.eqsubst_asm_tac ctxt [0] @{thms word_nat_simps}

  val ltac_subst_simps_tac : Proof.context -> int -> tactic = fn ctxt =>
     EqSubst.eqsubst_tac ctxt [0] @{thms word_nat_simps}

  val ltac_core : Proof.context -> int -> tactic = fn ctxt =>
   IF' (find_metaimp_conclusion #> is_nat_or_word_lt) (
           ltac_defs_tac ctxt
   ORELSE' ltac_intros_tac ctxt
   ORELSE' ltac_simps_tac ctxt
   ORELSE' ltac_elims_tac ctxt
   ORELSE' ltac_subst_simps_asm_tac ctxt
   ORELSE' ltac_subst_simps_tac ctxt
   ORELSE' Lin_Arith.tac ctxt
   ORELSE' Crush.crush_branch_clarsimp_tac ctxt)

  val ltac : Proof.context -> bool -> int -> tactic = fn ctxt => fn filtered =>
     if filtered then IF' (find_metaimp_conclusion #> is_nat_or_word_lt)
         (SOLVED' (filter_arithmetic_premises_tac ctxt THEN' REPEAT_ALL_NEW (ltac_core ctxt)))
     else
        REPEAT_ALL_NEW (ltac_core ctxt)

  val ltac_full : Proof.context -> int -> tactic = fn ctxt =>
     ltac ctxt true ORELSE' ltac ctxt false

end

(* Isar *)

local
  val _ = Theory.setup (Method.setup @{binding "filter_arithmetic_premises"}
              (Scan.succeed (SIMPLE_METHOD' o Crush_Arith.filter_arithmetic_premises_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "ltac"}
              (Scan.succeed (SIMPLE_METHOD' o Crush_Arith.ltac_full)) "")


in end