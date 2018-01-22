(* this type "a" will aready be given . 
    It's the alphabet over which a* is defined
*)
type a = Constructor of char


(* and a = Constructor of char *)
type a_star  = None | Character of a | Concatenation of a_star * a_star  

(* representation or after meaning is given to a_star, it becomes editable_string *)
type editable_string = { mutable str : a list ;mutable marker: int ; mutable length: int}

exception Empty

(* from type a_str , return an editable_string *)
let meaning a_st = 
    let rec evaluate a_st = match a_st with
            None -> []
        |   Character a -> [a]
        |   Concatenation (a_st1,a_st2) -> (evaluate a_st1) @ (evaluate a_st2) in
    let listOfA = evaluate a_st in
    let es = {str = listOfA ; marker = 0; length = List.length listOfA } in
    es

(* es stands for editable string *)
let lgh es = match es with
        {str = cl ; marker=m; length = l} -> l


let nonempty es = match es with
        {str=s ; marker=m; length = 0} ->false
    |   _ -> true


(* returns (a list)  from ocaml string  [It's a helper function] *)
let explodeCustom s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ( (Constructor s.[i]) :: l) in (*because Constructor of char gives the type a*)
  exp (String.length s - 1) []


(* converts ocaml string to "Editable string" *)
 (* initial position of the edit marker being 0 *)
let create str = 
    let l = String.length str in    
    let es = { str = explodeCustom str ; marker = 0 ; length = l  } in
    es        



(*  Time Complexity: O(es1.length)[because of @ operator defination] .
    To prove :lgh( concat s1 s2) = lgh(s1) + lgh(s2).
    In my implementation we have lgh(editable_string) = value of the length field and in the function defination I am directly 
        adding the two lengths, Hence proved.
    Otherwise it is proved with the @ operator defination. 
*)
let concat es1 es2 = 
    let es = { str =  es1.str @ es2.str  ; marker = 0 ; length = es1.length + es2.length } in
    es


 (* Time Complexity: O(lgh(s)). 
    To prove:  lgh(reverse s) = lgh(s). 
    In my implementation we have lgh(editable_string) = value of the length field and in the function defination I am directly 
        adding the two lengths, Hence proved.
    Otherwise the List.rev function preserves the lenght of the list (given in documentation)
 *)
let reverse es = 
    let res = { str = List.rev es.str ; marker = if es.length <=0  then 0 else (es.length - 1 - es.marker) ; length = es.length} in
    res


 (* Time Complexity: O(1) *)
let first es = match es with
        {str=s ; marker=m; length = 0} -> raise (Empty)
    |   {str=s ; marker=m; length = l} -> List.hd s


 (* Time Complexity: O(lgh s) because of List.nth (l - 1)
    We can do it in order 1 if while creating the string, we store the last character as an extra field in the editable_string record
    That will shift the computation time from here to creation of editable string object from ocaml string 
    Moreover, I have increased efficiency by storing and modifying the length and not calculating it everytime.
  *)
let last es = match es with
        {str=s ; marker=m; length = 0} -> raise (Empty )
    |   {str=s ; marker=m; length = l} -> List.nth s (l-1)



(* forward: When a marker points to the kth position in the string moves it to the (k+1)-th position, if it exists, and raising AtLast otherwise. 
    Time Complexity: O(1) 
 *)
exception AtLast
let forward es = 
    if (es.marker >= es.length - 1) then raise AtLast
    else es.marker <- es.marker + 1


(* back: When the marker points to the kth position in the string moves it to the (k-1)-th position, if it exists, and raising AtFirst otherwise.
   Time Complexity: O(1)  
*)
exception AtFirst
let back es = 
    if (es.marker <= 0 ) then raise AtFirst
    else es.marker <- es.marker - 1

(* moveTo: Given a non-negative integer n and a string s, moves the marker to the nth letter of s, counting from 0.  If n >= lgh s, then raise exception TooShort.
   Time Complexity: O(1) ] 
 *)
exception TooShort
let moveTo n es = 
    if (n >= es.length) then raise TooShort
    else es.marker <- n

(* helper function for replace *)
let rec repElem list pos elem list2 idx =
  match list with
    [] -> list2
  | h::t -> if (idx = pos) then list2@[elem]@t
            else
                repElem t pos elem (list2 @ [h]) (idx+1)

(* replace: which (assuming the marker is at a position n>= 0) in a string s, and a letter w, replaces the letter at the marker position of s with w.
  To Prove: lgh(replace w s) = lgh(s).
  Proof: In my implementation I am not modifying the length field , hence proved
  Otherwise by list property of substitution, we have that the lenght remains same.
*)
let replace w es = 
    es.str <- repElem es.str es.marker w [] 0


(* let () = print_string "Execution complete\n";; *)

