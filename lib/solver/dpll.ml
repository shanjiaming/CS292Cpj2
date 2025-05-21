(** Davis-Putnam-Logemann-Loveland (DPLL) solver *)

open Base

exception Solver_error

(* Make a solver given a CNF problem description *)
module Make (Problem : sig
  val desc : Description.t
end) =
struct
  (* the set of all variables *)
  let vars = Formula.vars Problem.desc.f

  (* the number of variables *)
  let num_vars = Set.length vars

  (* all clauses in the CNF problem *)
  let cs : Formula.t = Problem.desc.f

  (** Construct a resolution proof of the current (partial) decision assignment *)
  let make_proof (a : Assign.t) (unsat : Clause.t) : Proof.t =
    Todo.part 4 "Dpll.make_proof" ~dummy:(Proof.fact unsat)
  let my_make_proof (a : Assign.t) (proof : Proof.t) : Proof.t =
    (* Start with the unsat clause *)
    (* Logs.debug (fun m -> m "make_proof: Assignment: %a" Assign.pp a); *)
    (* Logs.debug (fun m -> m "make_proof: Proof: %a" Proof.pp proof); *)
    (* Get all decision levels in sorted order *)
    let all_levels = 
      Map.data a.delta
      |> List.dedup_and_sort ~compare:Int.compare
    in
    
    (* For each level, resolve with the antecedent clauses of that level's literals *)
    let rec build_proof current_proof = function
      | [] -> current_proof
      | level :: rest ->
          (* Get the trail at this level *)
          match Assign.trail_exn a level with
          | exception Assign.Unassigned -> build_proof current_proof rest
          | trail -> 
              (* Get all literals at this level (decision + implied) *)
              let level_lits = trail.Assign.Trail.decision :: trail.Assign.Trail.implied in
              
              (* For each literal, try to resolve with its antecedent clause if it has one *)
              let folder acc lit =
                match Assign.antecedent a lit with
                | None -> 
                    (* Decision literals don't have antecedents *)
                    acc
                | Some antecedent_clause ->
                    (* Get the current clause we're working with *)
                    let current_clause = Proof.replay acc in
                    
                    (* Try to find a resolution literal *)
                    match Set.find current_clause ~f:(fun l -> 
                      Set.mem antecedent_clause (Lit.negate l)
                    ) with
                    | Some resolve_lit ->
                        (* Logs.debug (fun m -> m "Resolving on literal: %a" Lit.pp resolve_lit); *)
                        (* Logs.debug (fun m -> m "Current clause: %a" Clause.pp current_clause); *)
                        (* Logs.debug (fun m -> m "Antecedent clause: %a" Clause.pp antecedent_clause); *)
                        Proof.resolve ~left:acc ~on:resolve_lit ~right:(Proof.fact antecedent_clause)
                    | None -> 
                        (* No resolution possible with this antecedent *)
                        acc
              in
              (* Process all literals at this level *)
              let new_proof = List.fold level_lits ~init:current_proof ~f:folder in
              build_proof new_proof rest
    in
    
    let proof = build_proof proof all_levels in
    (* Logs.debug (fun m -> m "make_proof: Final proof: %a" Proof.pp proof); *)
    proof
  
  

  exception Backtrack of Proof.t
  exception Found_sat of State.t

  let rec solve (s : State.t) : State.t =


    (* Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"); *)
    (* Logs.debug (fun m -> m "State: %a" State.pp s); *)
    let r, a = Bcp.run s.level s.a cs in
    (* update assignment in the solver state  *)
    let s = { s with a } in
    match r with
    | Sat ->
        (* Logs.debug (fun m -> m "BCP: SAT"); *)
        s
    | Unsat c ->
        (* Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c); *)
        let proof = my_make_proof s.a (Proof.fact c) in
        (* Logs.debug (fun m -> m "Backtracking..."); *)
        (* Logs.debug (fun m -> m "Proof: %a" Proof.pp proof); *)
        raise (Backtrack proof)
    | Unknown -> (
        (* Logs.debug (fun m -> m "BCP: Unknown"); *)
        (* pick (opposite) decision literals for the left & the right
           branches of the decision tree *)
        let left =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
          match Heuristics.random_unassigned vars s.a with
          | None -> 
              (* No unassigned variables means we've assigned everything and no conflict, so SAT *)
              (* Logs.debug (fun m -> m "No unassigned variables, SAT"); *)
              raise (Found_sat s)
          | Some l -> l
        in
        let right = Lit.negate left in
        try
          (* decide [left] and solve *)
          (* Logs.info (fun m -> m "Deciding %a" Lit.pp left); *)
          solve (State.decide s left)
        with 
        | Found_sat s' -> 
            (* Found satisfying assignment in left branch, propagate it up *)
            raise (Found_sat s')
        | Backtrack left_proof ->
          (* Left branch is unsat, try the right branch *)
          (* Logs.info (fun m -> m "Left branch unsat, trying right branch: %a" Lit.pp right); *)
          let s' = State.decide s right in
          try 
            solve s'
          with 
          | Found_sat s'' -> 
              (* Found satisfying assignment in right branch, propagate it up *)
              raise (Found_sat s'')
          | Backtrack right_proof ->
            (* Both branches are unsat, so the current branch is unsat *)
            Logs.info (fun m -> m "Right branch also unsat, backtracking");
            
            (* Get the processed clauses *)
            let left_clause = Proof.replay left_proof in
            let right_clause = Proof.replay right_proof in
            
            (* Logs.debug (fun m -> m "Attempting resolution for backtrack."); *)
            (* Logs.debug (fun m -> m "  Left decision: %a -> Processed Proof Clause: %a" Lit.pp left Clause.pp left_clause); *)
            (* Logs.debug (fun m -> m "  Right decision: %a -> Processed Proof Clause: %a" Lit.pp right Clause.pp right_clause); *)

            let combined_proof =
              (* Handle cases where one or both clauses might be empty,
                 though ideally make_proof should prevent non-trivial empty clauses here.
                 If a branch proved empty clause directly, use that proof. *)
              begin
                (* Check if right decision literal is absent in left clause *)
                if not (Set.mem left_clause right) then begin
                    (* Logs.debug (fun m -> m "  Right decision %a not in processed left clause %a, using processed left proof directly." Lit.pp right Clause.pp left_clause); *)
                    left_proof
                end
                 (* Check if left decision literal is absent in right clause *)
                else if not (Set.mem right_clause left) then begin
                    (* Logs.debug (fun m -> m "  Left decision %a not in processed right clause %a, using processed right proof directly." Lit.pp left Clause.pp right_clause); *)
                    right_proof
                end
                 (* Otherwise, resolve using the right decision literal *)
                else begin
                    (* Logs.debug (fun m -> m "  Resolving on decision literal: %a" Lit.pp right); *)
                    Proof.resolve ~left:left_proof ~on:right ~right:right_proof
                end
              end
            in
            
            (* Process unit clauses one more time on the combined proof *)
            let final_proof = my_make_proof s.a combined_proof in
            
            raise (Backtrack final_proof))

  (** Solving result *)
  let result : Solution.t =
    try
      let s' = solve State.init in
      SATISFIABLE s'.a.nu
    with 
    | Found_sat s -> 
        (* Found a satisfying assignment *)
        SATISFIABLE s.a.nu
    | Backtrack proof ->
      (* backtracked to the initial level, so unsat overall *)
      (* Logs.debug (fun m -> m "Backtracked to the initial level"); *)
      UNSATISFIABLE (Script.make [] proof)
end

(** Run DPLL algorithm *)
let run (desc : Description.t) : Solution.t =
  (* create a solver module and run the solver *)
  let module Solver = Make (struct
    let desc = desc
  end) in
  (* get the solver result *)
  Solver.result
