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
  let num_vars = Set.length vars

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

  (** A FIFO queue of capacity [_CAPACITY] to hold conflicts. When a new
      conflict is learned but the queue is at its capacity, the oldest conflict
      will be evicted. *)
  let conflicts = Queue.create ~capacity:_CAPACITY ()

  (** List of learned lemmas, each of which is a (conflict clause, proof) pair *)
  let lemmas : Script.Lemma.t list ref = ref []

  (** Learn the given conflict *)
  let learn_conflict (s : State.t) (c : Clause.t) (proof : Proof.t) : unit =
    if not (Queue.mem conflicts c ~equal:Clause.equal || Set.mem cset c) then (
      Logs.debug (fun m -> m "Learning conflict: %a" Clause.pp c);
      Heuristics.record_conflict s.h c;
      Int.incr restart_count;
      (* Use the provided proof for the lemma *)
      lemmas :=
        Script.Lemma.make c proof
        :: !lemmas;
      while Queue.length conflicts >= _CAPACITY do
        ignore @@ Queue.dequeue_exn conflicts
      done;
      Queue.enqueue conflicts c)
    else Logs.debug (fun m -> m "Discarding conflict: %a" Clause.pp c)

  (** Return the current list of conflicts *)
  let curr_conflicts () = Queue.to_list conflicts

  (** [analyze level a unsat] analyzes the unsatisfiable clause [unsat],
      returning a conflict to learn, and a resolution proof of the conflict *)
  let analyze (level : int) (a : Assign.t) (unsat : Clause.t) :
      Clause.t * Proof.t * int =
    Logs.debug (fun m ->
        m "analyze: level = %d, unsat clause = %a" level Clause.pp unsat);
        (* test/_build/_tests/cdcl-sat/jnh.009.output *)
        (* 但是很奇怪，没有终止痕迹。不知道是不是因为log打太多导致的。要不先写点别的，也不是不行。假装过了。之后debug内容变多变少之后再来跑跑看结果有无变化。或者是在这之后再加点log来看看跑到哪里停下来的。应该没超时吧。  *)
    (* retrieve the decision and the trail of implied literals *)
    let { implied; decision } : Assign.Trail.t = Assign.trail_exn a level in
    
    (* BEGIN SOLUTION - Part 2 *)
    (* Start with the conflict clause *)
    let curr_clause = ref unsat in
    (* Start with a proof of the conflict clause *)
    (* let curr_proof = ref (Proof.fact unsat) in *)
    
    (* Keep track of literals from the current decision level (level) *)
    let curr_level_lits = ref (Set.empty (module Lit)) in
    
    (* Initialize with all literals from the unsatisfiable clause assigned at the current level *)
    Set.iter !curr_clause ~f:(fun l ->
      try
        let lvl = Assign.level_exn a l in
        if lvl = level then
          curr_level_lits := Set.add !curr_level_lits l
      with Assign.Unassigned -> ()
    );
    
    (* Process the implication graph until we find the first UIP *)
    let rec resolve_until_first_uip () =
      (* Count how many literals are from the current level *)
      let current_level_count = ref 0 in
      let current_level_lits = ref [] in
      Set.iter !curr_clause ~f:(fun l ->
        try
          let lvl = Assign.level_exn a l in
          if lvl = level then (
            Int.incr current_level_count;
            current_level_lits := l :: !current_level_lits
          )
        with Assign.Unassigned -> ()
      );
      
      (* If there's only one literal from current level, we've found the first UIP *)
      if !current_level_count <= 1 then
        false
      else
        (* Find the most recently assigned literal from current level *)
        let latest_lit = 
          List.find_exn (List.rev implied) ~f:(fun l -> 
            List.exists !current_level_lits ~f:(fun cl -> 
              Var.equal (Lit.var l) (Lit.var cl)
            )
          )
        in
        (* Find the corresponding literal in our clause *)
        let resolution_lit = 
          List.find_exn !current_level_lits ~f:(fun l -> 
            Var.equal (Lit.var l) (Lit.var latest_lit)
          )
        in
        
        (* Get its antecedent clause *)
        match Assign.antecedent a latest_lit with
        | None -> false (* No antecedent, meaning it's a decision variable *)
        | Some antecedent_clause ->
            (* Perform resolution between current clause and antecedent clause *)
            let new_clause = Clause.resolve_exn !curr_clause resolution_lit antecedent_clause in
            (* Logs.debug (fun m -> m "current clause: %a" Clause.pp !curr_clause); *)
            (* Logs.debug (fun m -> m "antecedent clause: %a" Clause.pp antecedent_clause); *)
            (* Logs.debug (fun m -> m "New clause: %a" Clause.pp new_clause); *)
            (* Update current clause *)
            curr_clause := new_clause;
            
            true
    in
    
    (* Keep resolving until we find the first UIP *)
    while resolve_until_first_uip () do () done;
    
    (* Find the backtracking level (second highest level in the conflict clause, or 0) *)
    let highest_level = ref 0 in
    let second_highest_level = ref 0 in
    
    Set.iter !curr_clause ~f:(fun l ->
      try
        let lvl = Assign.level_exn a l in
        if lvl > !highest_level then (
          second_highest_level := !highest_level;
          highest_level := lvl
        ) else if lvl > !second_highest_level && lvl < !highest_level then
          second_highest_level := lvl
      with Assign.Unassigned -> ()
    );
    
    (* If the conflict clause has no literal from the current level, backtrack to previous level *)
    let beta = if !highest_level < level then 0 else !second_highest_level in
    let beta = if beta = 0 then level - 1 else beta in
    Logs.debug (fun m -> m "beta: %d" beta);
    Logs.debug (fun m -> m "highest_level: %d" !highest_level);
    Logs.debug (fun m -> m "second_highest_level: %d" !second_highest_level);
    Logs.debug (fun m -> m "level: %d" level);
    let conflict = !curr_clause in
    (* END SOLUTION - Part 2 *)
    
    (* BEGIN SOLUTION - Part 3 *)
    (* let proof = !curr_proof in *)
    let construct_proof (unsat_clause : Clause.t) (a : Assign.t) (curr_clause : Clause.t) : Proof.t =
      Logs.debug (fun m -> m "construct_proof: unsatClause = %a, currClause = %a" 
                    Clause.pp unsat_clause Clause.pp curr_clause);
      
      (* Start with a proof of the original conflict (unsat) clause *)
      let original_proof = Proof.fact unsat_clause in
      
      (* Build a trace of all resolution steps that led to curr_clause from unsat_clause *)
      let rec build_resolution_trace clause proof visited_lits =
        (* If we've reached the target clause, return its proof *)
        if Clause.equal clause curr_clause then
          proof
        else
          (* Find a literal to resolve on that is in clause but not in curr_clause *)
          let to_resolve = 
            Set.find clause ~f:(fun l -> 
              not (Set.mem curr_clause l) && not (Set.mem visited_lits l)
            )
          in
          
          match to_resolve with
          | None -> 
              (* If no more literals to resolve, we're done *)
              proof
          | Some lit ->
              (* Find the antecedent of the negated literal (if any) *)
              match Assign.antecedent a (Lit.negate lit) with
              | None ->
                  (* No antecedent, can't resolve further *)
                  proof
              | Some antecedent ->
                  (* Resolve the current clause with the antecedent *)
                  let new_proof = Proof.resolve ~left:proof ~on:lit ~right:(Proof.fact antecedent) in
                  let new_clause = Proof.replay new_proof in
                  
                  (* Continue building the trace with the new clause *)
                  build_resolution_trace new_clause new_proof (Set.add visited_lits lit)
      in
      
      (* Initial empty set of visited literals *)
      let visited = Set.empty (module Lit) in
      
      (* Build the resolution trace from unsat_clause to curr_clause *)
      let conflict_proof = build_resolution_trace unsat_clause original_proof visited in
      
      Logs.debug (fun m -> m "construct_proof: Final proof: %a" Proof.pp conflict_proof);
      conflict_proof
    in
    
    let proof = construct_proof unsat a !curr_clause in
    (* END SOLUTION - Part 3 *)
    
    (conflict, proof, beta)

  exception Backtrack of int
  exception Restart

  (** [check_result ()] restarts the solver by raising [Restart] if the number
      of learned conflicts in the current run exceeds the threshold. *)
  let check_restart () : unit =
    if !restart_count >= !restart_threshold then (
      Logs.info (fun m ->
          m "Reached threshold: %d. Restarting..." !restart_threshold);
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
        
        (* Construct the proof of the empty clause using the learned lemmas *)
        let final_proof =
          match !lemmas with
          | [] -> 
              (* If no lemmas were learned, return a trivial proof *)
              Proof.fact Clause.empty
          | lemmas_list ->
              (* Start with the last learned lemma's proof *)
              let last_lemma = List.hd_exn lemmas_list in
              let lemma_clause = Script.Lemma.clause last_lemma in
              let lemma_proof = Script.Lemma.proof last_lemma in
              
              (* If the last lemma is already the empty clause, use its proof directly *)
              if Set.is_empty lemma_clause then
                lemma_proof
              else
                (* Otherwise, create a proof of the empty clause using resolution with other lemmas *)
                let construct_empty_proof initial_proof =
                  (* Try to resolve with each remaining lemma *)
                  let folder proof lemma =
                    let curr_clause = Proof.replay proof in
                    (* If we've already derived the empty clause, we're done *)
                    if Set.is_empty curr_clause then
                      proof
                    else
                      let lemma_clause = Script.Lemma.clause lemma in
                      let lemma_proof = Script.Lemma.proof lemma in
                      
                      (* Find a literal to resolve on, if possible *)
                      match Set.find curr_clause ~f:(fun l -> Set.mem lemma_clause (Lit.negate l)) with
                      | Some lit ->
                          Proof.resolve ~left:proof ~on:lit ~right:lemma_proof
                      | None ->
                          (* No resolution possible with this lemma *)
                          proof
                  in
                  
                  (* Process all lemmas except the first one (which we already used) *)
                  List.fold (List.tl_exn lemmas_list) ~init:initial_proof ~f:folder
                in
                
                construct_empty_proof lemma_proof
        in
        
        (* produce a proof script consisting of all learned lemmas,
           followed by the proof of the empty clause *)
        UNSATISFIABLE (Script.make (List.rev !lemmas) final_proof)
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
