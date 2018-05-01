type constant = string
type variable = string * int
type term =
  | Var of variable             
  | Const of constant           
  | App of constant * term list 
type atom = Fail | Cut | Atom of  constant * term list
type clause = atom list
type assertion = atom * clause
type environment = (variable * term) list
type database = assertion list
type toplevel_cmd =
  | Assert of assertion  (** Assertion [a :- b_1, ..., b_n.] or [a.] *)
  | Goal of clause       (** Query [?- a] *)
      
let rec lookup env x =
  try List.assoc x env with Not_found -> Var x

let rec subst_term env = function
  | Var x as e ->
      (let e' = lookup env x in
	 if e = e' then e' else subst_term env e')
  | Const _ as e -> e
  | App (c, ls) -> App (c, List.map (subst_term env) ls)	

let rec string_of_term = function
  | Var (v, 0) -> v
  | Var (v, n) -> v ^ string_of_int n
  | Const c -> c
  | App (f, ls) -> f ^ "(" ^ (String.concat ", " (List.map string_of_term ls)) ^ ")"

let string_of_env env =
  match List.filter (fun ((_, n), _) -> n = 0) env with
    | [] -> "Yes"
    | env' -> String.concat "\n"
	(List.map
	   (fun ((x,n), e) ->
	      x ^ " = " ^ string_of_term (subst_term env e))
	   (List.rev env'))

let rec occurs x = function
    Var y -> x = y
  | Const _ -> false
  | App (_, ts) -> List.exists (occurs x) ts
