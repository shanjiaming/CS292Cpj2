open Base

type status = Sat | Unsat | Unit of Lit.t | Unresolved

let status (nu : Eval.t) (c : Clause.t) : status =
  match
    List.partition3_map (Set.to_list c) ~f:(fun l ->
        match Eval.lit nu l with
        | Some false -> (* false *) `Fst l
        | None -> (* unassigned *) `Snd l
        | Some true -> (* true *) `Trd l)
  with
  | _, _, _ :: _ -> Sat (* At least one literal is true *)
  | _, [], [] -> Unsat (* All literals are false *)
  | _, [una], [] -> Unit una (* All literals but one are false, and one is unassigned *)
  | _, _, [] -> Unresolved (* No literals are true, and at least two are unassigned *)

type result = Unsat of Clause.t | Unknown | Sat

let run (level : int) (a : Assign.t) (cs : Clause.t list) : result * Assign.t =
  (* Extract nu from assignment *)
  
  (* Check if all clauses are satisfied *)
  let all_satisfied = 
    List.for_all cs ~f:(fun c -> 
      match status a.nu c with 
      | Sat -> true 
      | _ -> false
    )
  in
  
  if all_satisfied then
    (* Find all variables in cs that are unassigned in a *)
    let unassigned_vars = 
      List.fold cs ~init:(Set.empty (module Var)) ~f:(fun acc_vars c ->
        Set.fold c ~init:acc_vars ~f:(fun vars l ->
          match Eval.lit a.nu l with
          | None -> Set.add vars (Lit.var l)
          | Some _ -> vars
        )
      )
    in
    (* Logs.debug (fun m -> m "BCP Initial Check: all_satisfied=true. Unassigned vars in clauses: %a" Fmt.(list Var.pp) (Set.to_list unassigned_vars)); *)
    if Set.is_empty unassigned_vars then
      (* All relevant vars assigned, truly Sat for BCP context *)
      begin
        (* Logs.debug (fun m -> m "BCP Initial Check: Returning Sat, no unassigned vars."); *)
        Sat, a
      end
    else
      (* Assign all unassigned vars to true as implications *)
      begin
        (* Logs.debug (fun m -> m "BCP Initial Check: Assigning %d unassigned vars positive as implications..." (Set.length unassigned_vars)); *)
        let final_a = 
          Set.fold unassigned_vars ~init:a ~f:(fun current_a var ->
            (* Use assign_implied with an empty clause as the reason *)
            Assign.assign_implied current_a level Clause.empty (Lit.make_pos var)
          )
        in
        (* Logs.debug (fun m -> m "BCP Initial Check: Returning Sat, final assignment: %a" Assign.pp final_a); *)
        Sat, final_a
      end
  else
    begin
      (* Logs.debug (fun m -> m "BCP Initial Check: all_satisfied=false. Proceeding to propagation."); *)
      (* Check for initial conflict first before starting BCP loop *)
      let initial_unsat_clause =
        List.find cs ~f:(fun c -> 
          match status a.nu c with 
          | Unsat -> true 
          | _ -> false
        )
      in
      match initial_unsat_clause with
      | Some c -> 
          (* Logs.debug (fun m -> m "BCP Initial Check: Found initial conflict: %a" Clause.pp c); *)
          Unsat c, a
      | None ->
          let rec bcp assign =
            (* Logs.debug (fun m -> m "BCP loop: Current assignment: %a" Assign.pp assign); *)
            let { Assign.nu = curr_nu; _ } = assign in
            let unit_clauses =
              List.filter_map cs ~f:(fun c ->
                match status curr_nu c with
                | Sat -> None
                | Unsat -> Some (Lit.dummy, c) (* Using dummy literal to represent unsat *)
                | Unit l -> Some (l, c)
                | Unresolved -> None)
            in
            (* Logs.debug (fun m -> m "BCP loop: Found %d unit/unsat clauses." (List.length unit_clauses)); *)
            (* Optionally log the clauses themselves if needed, could be verbose *) 
            (* Logs.debug (fun m -> m "BCP loop: Unit/Unsat pairs: %a" Fmt.(list (pair Lit.pp Clause.pp)) unit_clauses); *)
            
            match unit_clauses with
            | [] -> 
                (* Propagation finished. Log final status before returning Unknown *)
                let final_status_satisfied = 
                  List.for_all cs ~f:(fun c -> 
                    match status assign.nu c with 
                    | Sat -> true 
                    | _ -> false
                  )
                in
                let remaining_unassigned_in_clauses = 
                  List.fold cs ~init:(Set.empty (module Var)) ~f:(fun acc_vars c ->
                    Set.fold c ~init:acc_vars ~f:(fun vars l ->
                      match Eval.lit assign.nu l with
                      | None -> Set.add vars (Lit.var l)
                      | Some _ -> vars
                    )
                  )
                in
                (* Logs.debug (fun m -> m "BCP loop end check: All clauses satisfied? %b" final_status_satisfied); *)
                (* Logs.debug (fun m -> m "BCP loop end check: Unassigned vars in clauses: %a" Fmt.(list Var.pp) (Set.to_list remaining_unassigned_in_clauses)); *)
                
                (* Decide return value based on satisfaction status *)
                if final_status_satisfied then
                  begin
                    (* Logs.debug (fun m -> m "BCP loop: No more unit clauses. All clauses SAT. Returning Sat."); *)
                    Sat, assign
                  end
                else
                  begin
                    (* Logs.debug (fun m -> m "BCP loop: No more unit clauses. Clauses not SAT. Returning Unknown."); *)
                    Unknown, assign
                  end
            | (l, c) :: _ ->
                if Lit.equal l Lit.dummy then
                  begin
                    (* Logs.debug (fun m -> m "BCP loop: Found conflict: %a" Clause.pp c); *)
                    Unsat c, assign (* Conflict detected *)
                  end
                else
                  begin
                    (* Logs.debug (fun m -> m "BCP loop: Propagating literal %a from clause %a" Lit.pp l Clause.pp c); *)
                    let assign' = Assign.assign_implied assign level c l in
                    (* Logs.debug (fun m -> m "BCP: assign: %a" Assign.pp assign'); *)
                    bcp assign' (* Continue BCP with updated assignment *)
                  end
          in
          bcp a (* Start the BCP loop *)
    end
