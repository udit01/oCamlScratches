exception Empty

let rec last l = match l with
        [] -> raise Empty
    |   h::t -> if t = [] then h else last t

(* --------------------------------------------------------------------- *)

let rec last_two l = match l with
        [] -> None
    |   [x] -> Single x
    |   [x;y] -> Double (x,y)
    |   _::t -> last_two t

(* --------------------------------------------------------------------- *)

let rec at l num = match num with 
        0 -> Some (List.hd l)
    |    _ -> at (List.tl l) (num-1)

(* --------------------------------------------------------------------- *)

let nElem l = 
    let rec ne l count = match l with 
        []  -> count 
        | h::t -> ne t (count+1)   in
    ne l 0

(* --------------------------------------------------------------------- *)

let rev l = 
    let rec r li lf = match li with
        [] -> lf
        | h::t -> r t ( [h] @lf) in
    r l []

(* --------------------------------------------------------------------- *)

let is_palindrome l = 
    let rl = rev l in
        let rec cmp l1 l2 = match l1 with 
            [] -> if l2 = [] then true else false
            | h::t -> (match l2 with 
                        [] -> false
                        | h2::t2 -> if h2 = h then cmp t t2 else false ) in
    cmp l rl


let is_palindrome2 list =
    list = List.rev list


(* --------------------------------------------------------------------- *)

type 'a node =
    | One of 'a 
    | Many of 'a node list;;


let rec flatten l = match l with
    [] -> []
    | (One x ):: t -> [x] @ (flatten t)
    | (Many l2):: t -> (flatten l2) @ (flatten t)

(* --------------------------------------------------------------------- *)

(* what does AS keyword do ? *)
let rec compress = function
    | a :: (b :: _ as t) -> if a = b then compress t else a :: compress t
    | smaller -> smaller;;


(* --------------------------------------------------------------------- *)
(* ----pack funcion *)


