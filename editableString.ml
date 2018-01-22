(* this type "a" will aready be given *)
type a = Constructor of char


(*would be a list of a ?*)
type a_star  = None | Character of a | Concatenation of a_star * a_star  
(* and a = Constructor of char;; *)

type editable_string = { mutable str : a list ;mutable marker: int ;mutable length: int}

exception Empty of string

(* from type a_star , return a list of characters *)
let rec meaning a_st = match a_st with
        None -> []
    |   Character a -> [a]
    |   Concatenation (a_st1,a_st2) -> (meaning a_st1) @ (meaning a_st2)

(* esw stands for editable string wrapper *)
let lgh esw = match esw with
        {str = cl ; marker=m; length = l} -> l
        
        (* None -> 0 
    |   Character a -> 1
    |   Concatenation (s1,s2) -> (lgh s1) + (lgh s2) *)


let nonempty esw = match esw with
        {str=s ; marker=m; length = 0} ->false
    |   _ -> true


(* returns a list of from string  *)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ( (Constructor s.[i]) :: l) in
  exp (String.length s - 1) [];;


(* converts ocaml string to "Editable string" *)
 (* initial position of the edit marker being 0 *)
let create str = 
    let l = String.length str in    
    let esw = { str = explode str ; marker = 0 ; length = l  } in
    esw        



(*  What is its complexity? Also prove that lgh( concat s1 s2) = lgh(s1) + lgh(s2).*)
let concat esw1 esw2 = 
    let esw = { str =  esw1.str @ esw2.str  ; marker = 0 ; length = esw1.length + esw2.length } in
    esw


 (* Its complexity should be O(lgh(s)).  Also prove that  lgh(reverse s) = lgh(s). *)
let reverse esw = 
    let resw = { str = List.rev esw.str ; marker = esw.length - 1 - esw.marker ; length = esw.length} in
    resw


 (* [ This should be O(1). ] *)
let rec first esw = match esw with
        {str=s ; marker=m; length = 0} -> raise (Empty "No first element because string is empty!")
    |   {str=s ; marker=m; length = l} -> List.hd s


 (* [ This should be O(1). ] *)
let rec last esw = match esw with
        {str=s ; marker=m; length = 0} -> raise (Empty "No last element because string is empty!")
    |   {str=s ; marker=m; length = l} -> List.nth s (l-1)



(* forward: When a marker points to the kth position in the string moves it to the (k+1)-th position, if it exists, and raising AtLast otherwise. [Complexity? Should be O(1). *)
exception AtLast
let forward esw = 
    if (esw.marker >= esw.length - 1) then raise AtLast
    else esw.marker <- esw.marker + 1
(* should the above function return a new object? *)

(* back: When the marker points to the kth position in the string moves it to the (k-1)-th position, if it exists, and raising AtFirst otherwise. [Complexity? Should be O(1). ] *)
exception AtFirst
let back edStrW = 
    if (edStrW.marker <= 0 ) then raise AtFirst
    else edStrW.marker <- edStrW.marker - 1

(*moveTo: Given a non-negative integer n and a string s, moves the marker to the nth letter of s, counting from 0.  If n >= lgh s, then raise exception TooShort.  [ Complexity? Should be O(n), where n is the given argument. ] *)
exception TooShort
exception Nout of string
let moveTo n edStrW = 
    if (n >= edStrW.length) then raise TooShort
    else if (n<0) then raise (Nout "n cannot be negative")
    else edStrW.marker <- n

(* replace: which (assuming the marker is at a position n>= 0) in a string s, and a letter w, replaces the letter at the n-th position of s with w.  [ Prove that lgh(replace w s) = lgh(s). ] *)
(* assume the arguents are given correctly *)

let rec repElem list pos elem list2 idx =
  match list with
    [] -> list2
  | h::t -> if (idx = pos) then list2@[elem]@t
            else
                repElem t pos elem (list2 @ [h]) (idx+1)

let replace w esw = 
    (* let repEsw = {str = repElem esw.str esw.marker w [] 0  ; marker = esw.marker  ; length = esw.length} in
    repEsw *)
    esw.str <- repElem esw.str esw.marker w [] 0



let () = print_string "Execution complete\n";;

