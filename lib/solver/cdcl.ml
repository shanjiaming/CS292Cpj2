(** Conflict-driven clause learning (CDCL) solver *)

open Base

exception Solver_error

(* Make a solver given a CNF problem description *)
module Make (Problem : sig
  val desc : Description.t
end) =
struct
  (* The set of all variables *)
  let vars = Formula.vars Problem.desc.f

  (** The number of variables *)
  (* let num_vars = Set.length vars *) (* Warning 32 [unused-value-declaration]: unused value num_vars. *)

  (** Restart threshold *)
  let restart_threshold = ref 1

  (** Restart increment strategy: multiply the threshold by 2 each time *)
  let restart_inc n = n * 2

  (** Restart count *)
  let restart_count = ref 0

  (** All original clauses in the CNF problem *)
  let cs : Formula.t = Problem.desc.f

  (** Set of all original clauses *)
  let cset = Set.of_list (module Clause) cs

  (** Allow the same number of conflicts as the number of original clauses. Feel
      free to change this parameter. *)
  let _CAPACITY = List.length cs

  (** A FIFO queue to hold learned conflicts for BCP. *)
  let conflicts_queue : Clause.t Queue.t = Queue.create ()

  (** A set mirroring the contents of [conflicts_queue] for efficient membership testing. *)
  let conflicts_set : (Clause.t, Clause.comparator_witness) Set.t ref = ref (Set.empty (module Clause))

  (** Internal record to store lemma info alongside the opaque Script.Lemma.t *)
  type internal_lemma_info = {
    goal_clause : Clause.t;
    proof_object : Proof.t;
    script_lemma_obj : Script.Lemma.t
  }

  (** List of learned lemmas, each storing the goal, proof, and the Script.Lemma.t obj *)
  let lemmas : internal_lemma_info list ref = ref []

  (** Learn the given conflict *)
  let learn_conflict (s : State.t) (c : Clause.t) (proof : Proof.t) : unit =
    let is_original = Set.mem cset c in
    let already_learned_and_active = if Set.is_empty c then false else Set.mem !conflicts_set c in

    if (not is_original && not already_learned_and_active) || Set.is_empty c then (
      Heuristics.record_conflict s.h c;
      Int.incr restart_count;
      lemmas :=
        { goal_clause = c; proof_object = proof; script_lemma_obj = Script.Lemma.make c proof }
        :: !lemmas;
      if not (Set.is_empty c) then (
        if _CAPACITY > 0 then (
          if Queue.length conflicts_queue >= _CAPACITY then (
            let oldest_conflict = Queue.dequeue_exn conflicts_queue in
            conflicts_set := Set.remove !conflicts_set oldest_conflict
          );
          Queue.enqueue conflicts_queue c;
          conflicts_set := Set.add !conflicts_set c
        )
      );
      (* 每学到100个conflict输出一次进度 *)
      let learned = List.length !lemmas in
      if learned % 100 = 0 then
        Logs.app (fun m -> m "[Progress] Learned %d conflicts, restarts: %d, current level: %d" learned !restart_count s.level)
    )
    (* 其他日志全部注释掉 *)

  (** Return the current list of conflicts *)
  let curr_conflicts () = Queue.to_list conflicts_queue

  (** [analyze level a unsat] analyzes the unsatisfiable clause [unsat],
      returning a conflict to learn, and a resolution proof of the conflict *)
  let analyze (level : int) (a : Assign.t) (unsat : Clause.t) :
      Clause.t * Proof.t * int =
    Logs.debug (fun m ->
        m "analyze: level = %d, unsat clause = %a" level Clause.pp unsat);
    let { implied; _ (* decision was unused *) } : Assign.Trail.t = Assign.trail_exn a level in
    
    let curr_clause = ref unsat in
    
    (* Process the implication graph until we find the first UIP *)
    let resolve_until_first_uip () =
      let current_level_count = ref 0 in
      let current_level_lits_list = ref [] in
      Set.iter !curr_clause ~f:(fun l ->
        try
          let lvl = Assign.level_exn a l in
          if lvl = level then (
            Int.incr current_level_count;
            current_level_lits_list := l :: !current_level_lits_list
          )
        with Assign.Unassigned -> ()
      );
      
      if !current_level_count <= 1 then
        false
      else
        let latest_lit = 
          List.find_exn (List.rev implied) ~f:(fun l_implied -> 
            List.exists !current_level_lits_list ~f:(fun l_clause -> 
              Var.equal (Lit.var l_implied) (Lit.var l_clause)
            )
          )
        in
        let resolution_lit = 
          List.find_exn !current_level_lits_list ~f:(fun l_clause -> 
            Var.equal (Lit.var l_clause) (Lit.var latest_lit)
          )
        in
        
        match Assign.antecedent a latest_lit with
        | None -> 
            Logs.warn (fun m -> m "Resolve_until_first_uip: latest_lit %a at level %d has no antecedent. Stopping resolution." Lit.pp latest_lit level);
            false 
        | Some antecedent_clause ->
            (* Logs.debug (fun m -> m "Resolving UIP: %a with antecedent %a on %a" Clause.pp !curr_clause Clause.pp antecedent_clause Lit.pp resolution_lit); *)
            let new_clause = Clause.resolve_exn !curr_clause resolution_lit antecedent_clause in
            curr_clause := new_clause;
            true
    in
    
    while resolve_until_first_uip () do () done;
    
    let c_uip = !curr_clause in

    let highest_level = ref 0 in
    let second_highest_level = ref 0 in
    
    Set.iter c_uip ~f:(fun l ->
      try
        let lvl = Assign.level_exn a l in
        if lvl > !highest_level then (
          second_highest_level := !highest_level;
          highest_level := lvl
        ) else if lvl > !second_highest_level && lvl < !highest_level then
          second_highest_level := lvl
      with Assign.Unassigned -> ()
    );
    
    let beta = if !highest_level < level then 0 else !second_highest_level in
    let beta = if beta = 0 && level > 0 then level - 1 else if beta = 0 && level = 0 then -1 else beta in
    Logs.debug (fun m -> m "UIP clause: %a, beta: %d, highest_level: %d, second_highest: %d, current_level: %d" Clause.pp c_uip beta !highest_level !second_highest_level level);

    let construct_proof (original_unsat_clause : Clause.t) (current_assignment : Assign.t) (target_uip_clause : Clause.t) : Proof.t =
      Logs.debug (fun m -> m "construct_proof: original_unsat = %a, target_uip = %a" 
                    Clause.pp original_unsat_clause Clause.pp target_uip_clause);
      let proof_of_original_unsat = Proof.fact original_unsat_clause in
      let rec build_resolution_trace current_iter_clause current_iter_proof visited_lits =
        if Clause.equal current_iter_clause target_uip_clause then
          current_iter_proof
        else
          let to_resolve_opt = 
            Set.find current_iter_clause ~f:(fun l -> 
              not (Set.mem target_uip_clause l) && not (Set.mem visited_lits l)
            )
          in
          match to_resolve_opt with
          | None -> 
              Logs.warn (fun m -> m "construct_proof: Stuck building trace. Current: %a, Target: %a" Clause.pp current_iter_clause Clause.pp target_uip_clause);
              current_iter_proof 
          | Some lit_to_resolve ->
              match Assign.antecedent current_assignment (Lit.negate lit_to_resolve) with
              | None ->
                  Logs.warn (fun m -> m "construct_proof: No antecedent for %a (negation of %a). Current: %a, Target: %a" Lit.pp (Lit.negate lit_to_resolve) Lit.pp lit_to_resolve Clause.pp current_iter_clause Clause.pp target_uip_clause);
                  current_iter_proof 
              | Some antecedent ->
                  let new_proof = Proof.resolve ~left:current_iter_proof ~on:lit_to_resolve ~right:(Proof.fact antecedent) in
                  let resolved_clause = Proof.replay new_proof in 
                  build_resolution_trace resolved_clause new_proof (Set.add visited_lits lit_to_resolve)
      in
      let visited = Set.empty (module Lit) in
      build_resolution_trace original_unsat_clause proof_of_original_unsat visited
    in

    let proof_of_c_uip = construct_proof unsat a c_uip in
    
    let initial_decision_level = 0 in

    if beta < initial_decision_level && not (Set.is_empty c_uip) then (
      Logs.debug (fun m -> m "Conflict implies UNSAT. Resolving 1-UIP clause %a to empty." Clause.pp c_uip);
      let rec resolve_to_empty current_c current_p =
        if Set.is_empty current_c then
          (current_c, current_p)
        else
          let lit_in_c = Set.choose_exn current_c in 
          match Assign.antecedent a (Lit.negate lit_in_c) with
          | Some antecedent_clause ->
              Logs.debug (fun m -> m "Resolving to empty: %a with antecedent %a on %a" Clause.pp current_c Clause.pp antecedent_clause Lit.pp lit_in_c);
              let next_clause = Clause.resolve_exn current_c lit_in_c antecedent_clause in
              let next_proof = Proof.resolve ~left:current_p ~on:lit_in_c ~right:(Proof.fact antecedent_clause) in
              resolve_to_empty next_clause next_proof
          | None ->
              Logs.err (fun m -> m "UNEXPECTED: In resolve_to_empty, cannot find antecedent for %a (negation of %a from clause %a). This implies %a was likely a level 0 decision or an error in logic that should have been caught earlier (e.g. dummy var propagation)." Lit.pp (Lit.negate lit_in_c) Lit.pp lit_in_c Clause.pp current_c Lit.pp (Lit.negate lit_in_c) );
              (current_c, current_p)
      in
      let final_clause, final_proof = resolve_to_empty c_uip proof_of_c_uip in
      Logs.debug (fun m -> m "Resolved to final clause: %a for UNSAT proof." Clause.pp final_clause);
      if not (Set.is_empty final_clause) then
         Logs.warn (fun m -> m "Failed to resolve %a to empty clause for UNSAT, final clause is: %a" Clause.pp c_uip Clause.pp final_clause);
      (final_clause, final_proof, beta)
    ) else if Set.is_empty c_uip then (
      Logs.debug (fun m -> m "UIP analysis resulted directly in empty clause: %a." Clause.pp c_uip);
      (c_uip, proof_of_c_uip, beta)
    )
    else (
      Logs.debug (fun m -> m "Standard UIP case: clause %a, beta %d" Clause.pp c_uip beta);
      (c_uip, proof_of_c_uip, beta)
    )

  exception Backtrack of int
  exception Restart

  (** [check_result ()] restarts the solver by raising [Restart] if the number
      of learned conflicts in the current run exceeds the threshold. *)
  let check_restart () : unit =
    if !restart_count >= !restart_threshold then (
      Logs.app (fun m ->
          m "[Restart] Reached threshold: %d. Restarting..." !restart_threshold);
      restart_threshold := restart_inc !restart_threshold;
      restart_count := 0;
      raise Restart)

  let rec solve (s0 : State.t) : State.t =
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    Logs.debug (fun m -> m "Input state: %a" State.pp s0);
    Logs.debug (fun m -> m "Learned conflicts:");
    Logs.debug (fun m ->
        m "%a" Fmt.(vbox @@ list Clause.pp) (curr_conflicts ()));

    check_restart ();

    let r, a = Bcp.run s0.level s0.a (cs @ curr_conflicts ()) in
    (* update the assignment in the solver state *)
    let s = { s0 with a } in
    Logs.debug (fun m -> m "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
    Logs.debug (fun m -> m "State after unit-prop: %a" State.pp s);

    match r with
    | Sat ->
        Logs.debug (fun m -> m "BCP: SAT");
        s
    | Unsat c ->
        Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c);
        let c, proof, beta = analyze s.level s.a c in
        learn_conflict s c proof;
        Logs.debug (fun m -> m "Backtracking to level %d" beta);
        raise (Backtrack beta)
    | Unknown ->
        Logs.debug (fun m -> m "BCP: Unknown");
        let decision =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
(* z4: internal error, uncaught exception: *)
(* "No unassigned variable" *)
          Heuristics.best_unassigned vars s.a s.h
          |> Option.value_exn ~error:(Error.of_string "No unassigned variable")
        in
        
        (* BEGIN SOLUTION - Part 2 *)
        (* 每次主决策时输出当前决策层和trail长度 *)
        let { Assign.Trail.implied; _ } = Assign.trail_exn s.a s.level in
        let trail_len = 1 + List.length implied in
        Logs.app (fun m -> m "[Decide] Level: %d, Trail length: %d" s.level trail_len);
        let next_state = State.decide s decision in
        try
          solve next_state
        with Backtrack beta ->
          if beta < s.level then
            raise (Backtrack beta)
          else
            solve s
        (* END SOLUTION - Part 2 *)

  let rec run () : Solution.t =
    let s = State.init in
    try
      let s' = solve s in
      SATISFIABLE s'.a.nu
    with
    | Backtrack _ ->
        (* backtracked to the initial level, so unsat overall *)
        Logs.debug (fun m -> m "Backtracked to the initial level");
        
        let final_proof_opt =
          List.find_map !lemmas ~f:(fun ili -> (* renamed lemma to ili *)
              if Set.is_empty ili.goal_clause then Some ili.proof_object else None)
        in

        let final_proof =
          match final_proof_opt with
          | Some proof -> 
              Logs.debug (fun m -> m "Found proof for empty clause among internally stored lemmas.");
              proof
          | None ->
              Logs.err (fun m -> m "CDCL reached UNSAT state, but no lemma proving the empty clause was found in the learned set. This indicates an internal error.");
              Proof.fact Clause.empty 
        in
        
        let script_lemmas_list = List.map ~f:(fun ili -> ili.script_lemma_obj) (List.rev !lemmas) in
        UNSATISFIABLE (Script.make script_lemmas_list final_proof)
    | Restart ->
        (* restart the solver *)
        run ()

  (** Solving result *)
  let result = run ()
end

(** Run CDCL algorithm *)
let run (desc : Description.t) : Solution.t =
  (* create a solver module and run the solver *)
  let module Solver = Make (struct
    let desc = desc
  end) in
  Solver.result
