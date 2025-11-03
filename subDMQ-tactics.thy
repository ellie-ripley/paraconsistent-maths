(* Title: subDMQ-tactics.thy
   Author: almost entirely Vincent Jackson, with tiny tweaks by Ellie Ripley*)

theory "subDMQ-tactics"
  imports Pure "subDMQ"
begin

(* TODO: This currently depends on all of subDMQ. 
   But subDMQ.thy itself proves a bunch of stuff not needed here,
   and that it would be nice to have tactics for.
   Refactor: language and just the theorems needed for these tactics,
             then the tactics,
             then everything else
*)

ML \<open>

signature SUBDMQ_CLUNKY_TACTICS =
sig
  (* Raw tactics *)
  val norm_bientl_comm : Proof.context -> tactic;
  val norm_conj_comm : Proof.context -> tactic;
  val norm_conj_comm2 : Proof.context -> tactic;
  val norm_conj_assoc : Proof.context -> tactic;
  val norm_conj_assoc2 : Proof.context -> tactic;
  val norm_disj_comm : Proof.context -> tactic;
  val norm_disj_comm2 : Proof.context -> tactic;
  val norm_disj_assoc : Proof.context -> tactic;
  val norm_disj_assoc2 : Proof.context -> tactic;
  val norm_dn_strip : Proof.context -> tactic;
  val norm_dn_strip2 : Proof.context -> tactic;

  val subdmq_normalize_tac : Proof.context -> tactic;
end;

structure SubDMQClunkyTactics: SUBDMQ_CLUNKY_TACTICS =
struct

fun term_Vars (t : term) : (indexname * typ) list =
  fold_aterms
    (fn t => fn vs =>
      case t of
        Var xt => xt :: vs
      | _ => vs)
    t []

fun upper_tri_pairs [] = []
  | upper_tri_pairs (x :: xs) = map (fn x' => (x, x')) xs @ upper_tri_pairs xs;

fun gather_leaves gctxt (pat : term) (frame : term) ts =
  ts
  |> maps (fn tprem =>
      Unify.smash_unifiers gctxt [(frame $ pat, tprem)] Envir.init
      |> Seq.maps (fn env => Seq.of_list (map (Envir.lookup env) (term_Vars pat)))
      |> Seq.map_filter (Option.mapPartial (fn t =>
          case Seq.pull (Unify.smash_unifiers gctxt [(pat, t)] Envir.init) of
            SOME _ => NONE
          | NONE => SOME t))
      |> Seq.list_of)
  |> sort_distinct Term_Ord.fast_term_ord;

(* conj *)

fun norm_conj_assoc (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS (resolve_tac ctxt [@{thm conj_assoc_in_context}])));

fun norm_conj_assoc2 (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS (dresolve_tac ctxt [@{thm conj_assoc_in_context2}])));

fun norm_conj_comm_skel (resolver: Proof.context -> thm list -> int -> tactic) (vka : Vars.key) (vkb : Vars.key) (ctxt : Proof.context) (th : thm) : thm Seq.seq =
 let
    val frame = Var (("p", 0), @{typ \<open>o \<Rightarrow> o\<close>});
    val pat = @{const "subDMQ.conj"} $ Var (("a", 0), @{typ o}) $ Var (("b", 0), @{typ o});
    val leaves =
      Thm.prems_of th
      |> gather_leaves (Context.Proof ctxt) pat frame
      |> map (Thm.cterm_of ctxt);
    val leafpairs = upper_tri_pairs leaves |> (fn x => (@{print} "leafpairs "; x)) |> (fn x => (@{print} x; x))
  in
    REPEAT_DETERM (CHANGED (
      FIRSTGOAL (resolver ctxt
        ((maps
          (fn (ta, tb) =>
              (map
                (Thm.instantiate (TVars.empty, Vars.make2
                                                (vka, ta)
                                                (vkb, tb)))
               [ @{thm conj_left_comm_in_context}, @{thm conj_comm_in_context} ]))
          leafpairs) |> (fn x => (@{print} "conjcomm "; x)) |> (fn x => (@{print} x; x)))
    ))) th
  end;

val norm_conj_comm = norm_conj_comm_skel resolve_tac (("A", 0), @{typ o}) (("B", 0), @{typ o})
val norm_conj_comm2 = norm_conj_comm_skel dresolve_tac (("B", 0), @{typ o}) (("A", 0), @{typ o})


(* disj *)

fun norm_disj_assoc (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS (resolve_tac ctxt [@{thm disj_assoc_in_context}])));

fun norm_disj_assoc2 (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS (dresolve_tac ctxt [@{thm disj_assoc_in_context2}])));


fun norm_disj_comm_skel (resolver: Proof.context -> thm list -> int -> tactic) (vka : Vars.key) (vkb : Vars.key) (ctxt : Proof.context) (th : thm) : thm Seq.seq =
  let
    val frame = Var (("p", 0), @{typ \<open>o \<Rightarrow> o\<close>});
    val pat = @{const "subDMQ.disj"} $ Var (("a", 0), @{typ o}) $ Var (("b", 0), @{typ o});
    val leaves =
      Thm.prems_of th
      |> gather_leaves (Context.Proof ctxt) pat frame
      |> map (Thm.cterm_of ctxt);
    val leafpairs = upper_tri_pairs leaves
  in
    REPEAT_DETERM (CHANGED (EVERY (
      map
        (fn (ta, tb) =>
          FIRSTGOAL (resolver ctxt
            (map
              (Thm.instantiate (TVars.empty, Vars.make2
                                              (vka, ta)
                                              (vkb, tb)))
             [ @{thm disj_left_comm_in_context}, @{thm disj_comm_in_context} ])))
        leafpairs
    ))) th
  end;

val norm_disj_comm = norm_disj_comm_skel resolve_tac (("A", 0), @{typ o}) (("B", 0), @{typ o})
val norm_disj_comm2 = norm_disj_comm_skel dresolve_tac (("B", 0), @{typ o}) (("A", 0), @{typ o})

(* bientl *)

fun norm_bientl_comm (ctxt : Proof.context) (th : thm) : thm Seq.seq =
  let
    val frame = Var (("p", 0), @{typ \<open>o \<Rightarrow> o\<close>});
    val pat = @{const "subDMQ.bientl"} $ Var (("a", 0), @{typ o}) $ Var (("b", 0), @{typ o});
    val leaves =
      Thm.prems_of th
      |> gather_leaves (Context.Proof ctxt) pat frame
      |> map (Thm.cterm_of ctxt);
    val leafpairs = upper_tri_pairs leaves
  in
    CHANGED (EVERY (
      map
        (fn (ta, tb) =>
          FIRSTGOAL (resolve_tac ctxt
            (map
              (Thm.instantiate (TVars.empty, Vars.make2
                                              ((("A", 1), @{typ o}), ta)
                                              ((("B", 1), @{typ o}), tb)))
             [ @{thm bisub_rule[OF bientl_comm_bientl]} ])))
        leafpairs
    )) th
  end;

(* neg *)


fun norm_dn_strip (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS (resolve_tac ctxt [@{thm strip_dn_in_context}])));

fun norm_dn_strip2 (ctxt : Proof.context) : tactic =
  REPEAT_DETERM (CHANGED (ALLGOALS ((fn _ => print_tac ctxt "Here") THEN' (dresolve_tac ctxt [@{thm strip_dn_in_context2}]))));

(*
    1                      2           3
 (A1 \<Longrightarrow> A2 \<Longrightarrow> B)    (C \<Longrightarrow> D)    (E \<Longrightarrow> F)
-------------------------------------
  #P

*)

(* Normalise subdmq sentences. *)
val subdmq_normalize_tac =
    (fn c => print_tac c "One more pass") THEN'
    (norm_dn_strip #> TRY) THEN'
    (norm_dn_strip2 #> TRY) THEN'
    (norm_conj_assoc #> TRY) THEN'
    (norm_conj_assoc2 #> TRY) THEN'
    (norm_conj_comm #> TRY) THEN'
    (norm_conj_comm2 #> TRY) THEN'
    (norm_disj_assoc #> TRY) THEN'
    (norm_disj_assoc2 #> TRY) THEN'
    (norm_disj_comm #> TRY) THEN'
    (norm_disj_comm2 #> TRY) THEN'
    (norm_bientl_comm #> TRY);

end;

val _ =
  Theory.setup (
      Method.setup \<^binding>\<open>subdmq_clunky_normalize\<close>
        (Scan.succeed (fn ctxt => SIMPLE_METHOD (SubDMQClunkyTactics.subdmq_normalize_tac ctxt)))
        "normalise SubDMQ logic sentences")
\<close>

ML \<open>

signature SUBDMQ_BROKEN_TACTICS =
sig
  val subdmq_broken_normalize_tac : Proof.context -> tactic;
end;

structure SubDMQTactics: SUBDMQ_BROKEN_TACTICS =
struct

fun term_Vars (t : term) : (indexname * typ) list =
  fold_aterms
    (fn t => fn vs =>
      case t of
        Var xt => xt :: vs
      | _ => vs)
    t []

fun upper_tri_pairs [] = []
  | upper_tri_pairs (x :: xs) = map (fn x' => (x, x')) xs @ upper_tri_pairs xs;

fun gather_leaves gctxt (pat : term) (frame : term) ts =
  ts
  |> maps (fn tprem =>
      Unify.smash_unifiers gctxt [(frame $ pat, tprem)] Envir.init
      |> Seq.maps (fn env => Seq.of_list (map (Envir.lookup env) (term_Vars pat)))
      |> Seq.map_filter (Option.mapPartial (fn t =>
          case Seq.pull (Unify.smash_unifiers gctxt [(pat, t)] Envir.init) of
            SOME _ => NONE
          | NONE => SOME t))
      |> Seq.list_of)
  |> sort_distinct (Term_Ord.fast_term_ord #> rev_order);

fun get_pat_head (t : term): term =
  t |> Term.dest_comb |> snd |> Term.dest_comb |> snd |> Term.head_of

fun get_unordered_vars gctxt (a : term) (b : term): ((indexname * typ) * (indexname * typ)) list =
  let
    val (a_head, (a_frame, a_pat)) = a |> Term.dest_comb ||> Term.dest_comb
    val (b_head, (b_frame, b_pat)) = b |> Term.dest_comb ||> Term.dest_comb
  in
    (if not (Term_Ord.term_ord (a_head, b_head) |> is_equal)
      then raise ERROR "get_unordered_vars: outer pattern not equal"
    else if not (Term.is_Var a_frame andalso Term.is_Var b_frame)
      then raise ERROR "get_unordered_vars: frames are not schematic variables"
    else if not (Term_Ord.term_ord (a_frame, b_frame) |> is_equal)
      then raise ERROR "get_unordered_vars: frame not equal"
    else
      let val unordered_vars =
        (* assume there's at most one unification *)
        (case Unify.unifiers (gctxt, Envir.init, [(a_pat, b_pat)]) |> Seq.pull of
          SOME ((Envir.Envir {tenv, ...}, _), _) =>
            Vartab.dest tenv
            |> filter (fn (_,(_,t)) => Term.is_Var t)
            |> map (fn (x,(xty,t)) => ((x, xty), Term.dest_Var t))
        | NONE => []);
      in
        unordered_vars
      end)
  end;

fun ordered_equiv_in_context_thm
  (ctxt: Proof.context)
  (rw_thm: thm)
  (goal_th: thm): (thm list * thm list)
  =
  let
    val gctxt = Context.Proof ctxt;
    (* generate the left and right rewrite theorems
     * NOTE: we do both directions at the same time because we need to keep
     *       the ordering of the pairs consistent in both the forward and backward versions.
     *)
    val lr_rw_thm = @{thm equal_elim_rule1} OF [rw_thm];
    val rl_rw_thm = @{thm equal_elim_rule2} OF [rw_thm];
    (* find all variables in the rewrite theorem that need to be ordered for termination *)
    val uovars =
      get_unordered_vars gctxt (Thm.major_prem_of lr_rw_thm) (Thm.concl_of lr_rw_thm);
  in
    if List.null uovars then
      ([lr_rw_thm], [rl_rw_thm])
    else
      let
        (* dig out the pattern from the rewrite theorem *)
        (* TODO: currently assumes rewrite rules use only one connective,
                 that can be found at the head of the pattern. *)
        val pat_head: term = get_pat_head (Thm.major_prem_of lr_rw_thm)
        val pat_head_type = Term.type_of pat_head
        val (tyargs, _) = Term.strip_type pat_head_type
        val vargs = List.map (fn (i, ty) => Var (("a", i), ty)) (tag_list 1 tyargs)
        val pat = Term.list_comb (pat_head, vargs);
        (* collect leaves of this pattern *)
        val frame = Var (("p", 0), @{typ \<open>o \<Rightarrow> o\<close>});
        val leaves =
          Thm.prems_of goal_th
          |> gather_leaves gctxt pat frame
          |> map (Thm.cterm_of ctxt);
        val leafpairs = upper_tri_pairs leaves
        val (A, B) = List.hd uovars; (* TODO: need to do all of these *)
      in
        (* return the theorem, instantiatated with ordered pairs of terms found in goal thm *)
        (map
          (fn (ta, tb) =>
            lr_rw_thm
            |> Thm.instantiate (TVars.empty, Vars.make2 (A, ta) (B, tb)))
          leafpairs
        , map
          (fn (ta, tb) =>
            rl_rw_thm
            |> Thm.instantiate (TVars.empty, Vars.make2 (A, ta) (B, tb)))
          leafpairs
        )
      end
  end;

fun ordered_rw_thms ctxt prf_th =
  map_split
    (fn th => ordered_equiv_in_context_thm ctxt th prf_th)
    [ @{thm conj_left_comm_in_context3}
    , @{thm conj_assoc_in_context3}
    , @{thm conj_comm_in_context3}
    , @{thm disj_assoc_in_context3}
    , @{thm disj_left_comm_in_context3}
    , @{thm disj_comm_in_context3}
    , @{thm bientl_comm_in_context3}
    , @{thm dnbi_in_context3}]
  ||> flat |>> flat;

(* Normalise subdmq sentences. *)
fun subdmq_broken_normalize_tac ctxt =
    REPEAT_DETERM (CHANGED (FIRSTGOAL
      (fn i:int => fn th =>
        let val (r_thms, e_thms) = ordered_rw_thms ctxt th |> (fn x => (@{print} x; x))
        in (resolve_tac ctxt r_thms ORELSE' eresolve_tac ctxt e_thms) i th
        end)));

end;

val _ =
  Theory.setup (
      Method.setup \<^binding>\<open>subdmq_broken_normalize\<close>
        (Scan.succeed (fn ctxt => SIMPLE_METHOD (SubDMQTactics.subdmq_broken_normalize_tac ctxt)))
        "normalise SubDMQ logic sentences"
)
\<close>

lemma normalize_test: "P x \<otimes> P y \<Rrightarrow> u = v \<Longrightarrow> P y \<otimes> P x \<Rrightarrow> u = v"
proof -
  assume prem:"P x \<otimes> P y \<Rrightarrow> u = v"
  from prem show ?thesis by(subdmq_clunky_normalize)
qed

end