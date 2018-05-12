open Syntax

(** A value of type [choice] represents a choice point in the proof
    search at which we may continue searching for another solution. It
    is a tuple [(asrl, env, c, n)] where [asrl]
    for other solutions of clause [c] in environment [env], using
    assertion list [asrl], where [n] is the search depth. *)
type choice = database * environment * clause * int

(** The global database of assertions. *)
let base = ref ([] : database)

(** Add a new assertion at the end of the current database. *)
let assertz a = 
  let rec add = function [] -> [a] | b::bs -> b::(add bs) in
    (base := add !base)

(** Exception [NoSolution] is raised when a goal cannot be proved. *)
exception NoSolution

(** [renumber_term n t] renumbers all variable instances occurring in
    term [t] so that they have level [n]. *)
let rec renumber_term n = function
  | Var (x,_) -> Var (x,n)
  | Const _ as c -> c
  | App (c, ts) -> App (c, List.map (renumber_term n) ts)

(** [renumber_atom n a] renumbers all variable instances occurring in
    atom [a] so that they have level [n]. *)
let rec renumber_atom n (c,ts) = (c, List.map (renumber_term n) ts)

let rec display_solution ch env =
  match string_of_env env, ch with
    | "Yes", _ -> Printf.printf "YES@."
    | answer, [] -> Printf.printf "%s@." answer
    | answer, ch -> begin
      	Printf.printf "%s@.more? (y/n) [y]@?" answer;
      	match String.lowercase (read_line ()) with
      	  | "y" | "yes" | "" -> continue_search ch
      	  | _ -> raise NoSolution
      end

(** [continue_search ch] looks for other answers. It accepts a list of
    choices [ch]. It continues the search at the first choice in the
    list. *)
and continue_search = function
  | [] -> raise NoSolution
  | (asrl,env,gs,n)::cs -> solve cs asrl env gs n

(** [solve ch asrl env c n] looks for the proof of clause [c]. Other
    arguments are:
    
    [ch] is a list of choices at which we may look for other solutions,

    [asrl] is the list of assertions that are used to reduce [c] to subgoals,

    [env] is the current environment (values of variables),

    [n] is the search depth, which is increased at each level of search.

    When a solution is found, it is printed on the screen. The user
    then decides whether other solutions should be searched for.
*)
and solve ch asrl env c n =
  let rec reduce_atom a = function
    | [] -> None
    | (b,lst)::asrl' ->
	(try
	   let env' = Unify.unify_atoms env a (renumber_atom n b) in
	     Some (asrl', env', List.map (renumber_atom n) lst)
	 with Unify.NoUnify -> reduce_atom a asrl')
  in
    match c with
      | [] ->
	  (* All atoms are solved, we found a solution. *)
	  display_solution ch env
      | a::c' ->
	  (* Reduce the first atom in the clause. *)
	  (match reduce_atom a asrl with
	     | None -> 
		 (* This clause cannot be solved, look for other solutions. *)
		 continue_search ch
	     | Some (asrl', env', d) ->
		 let ch' = (asrl', env, c, n)::ch (* Add a new choice. *)
		 in
		   solve ch' (!base) env' (d @ c') (n+1) )

let solve_toplevel c =
  try
    solve [] (!base) [] c 1
  with NoSolution -> Printf.printf "No@."
