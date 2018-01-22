type a = Constructor of char

type a_star  = None | Stringify of a | Concatenation of a_star * a_star  
(* and a = Constructor of char;; *)
type edit_string = {str : a_star ; marker: int ; length: int}

exception Empty of string

let rec lgh s = match s with
        None -> 0 
    |   Stringify a -> 1
    |   Concatenation (s1,s2) -> (lgh s1) + (lgh s2)


let nonempty s = if s = None then false else true

(*  What is its complexity? Also prove that lgh( concat s1 s2) = lgh(s1) + lgh(s2).*)
let concat s1 s2 = Concatenation (s1,s2)
(* s1 and s2 are of type a_star *)


 (* Its complexity should be O(lgh(s)).  Also prove that  lgh(reverse s) = lgh(s). *)
(* let reverse s = 
    let reverse_s = create  *)


 (* [ This should be O(1). ] *)
let rec first s = match s with
        None -> raise (Empty "No first element because string is empty!")
    |   Stringify ch -> ch 
    |   Concatenation (s1,s2) -> first s1 


 (* [ This should be O(1). ] *)
let rec last s = match s with
        None -> raise (Empty "No last element because string is empty!")
    |   Stringify ch -> ch 
    |   Concatenation (s1,s2) -> last s1 

(* converts ocaml string to "Editable string" *)
 (* initial position of the edit marker being 0 *)
let create str = 
    let l = String.length str in    
    let edStr = None in
    let rec loop i = 
        if i >= l then edStr = Concatenation(edStr,None) 
        else edStr = Concatenation(edStr,str.[i]) ; loop (i+1) in
    let edStr = if l = 0 then None else (loop 0) in
    let edStrWrapper = { str = edStr ; marker = 0 ; length = l  } in
    edStrWrapper        
(* How create edit marker () ? *)

(* forward: When a marker points to the kth position in the string moves it to the (k+1)-th position, if it exists, and raising AtLast otherwise. [Complexity? Should be O(1). *)
let forward edStrW = 
    if (edStrW.marker >= edStrW.length - 1) then raise AtLast
    else edStrW.marker = edStrW.marker + 1


(* back: When the marker points to the kth position in the string moves it to the (k-1)-th position, if it exists, and raising AtFirst otherwise. [Complexity? Should be O(1). ] *)
let back edStrW = 
    if (edStrW.marker <= 0 ) then raise AtFirst
    else edStrW.marker = edStrW.marker - 1

(*moveTo: Given a non-negative integer n and a string s, moves the marker to the nth letter of s, counting from 0.  If n >= lgh s, then raise exception TooShort.  [ Complexity? Should be O(n), where n is the given argument. ] *)


(* replace: which (assuming the marker is at a position n>= 0) in a string s, and a letter w, replaces the letter at the n-th position of s with w.  [ Prove that lgh(replace w s) = lgh(s). ] *)

let str1 = "Hello!"
let str2 = "ProgrammingLanguages"



let () = print_string "Execution complete\n";;

