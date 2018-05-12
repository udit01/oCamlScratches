let (|>) x f = f x ;;

let l = [ ("one", "ONE", 1); ("two", "TWO" , 2 ); ("three", "THREE", 3) ] ;;
let kv = [ ("one", 1); ("two",2 ); ("three", 3) ] ;;
(* Why does the below thing shows syntax errors ? *)
(* List.Assoc.find l "two" ;; *)
(* Then use a deformed list and try to find it's elements, without type compatibility, use cutom things to confuse ocaml ? *)
(* List.assoc kv "one" ;; *)

open Core.Std

let build_counts () =
  In_channel.fold_lines stdin ~init:[] ~f:(fun counts line ->
    let count =
      match List.Assoc.find counts line with
      | None -> 0
      | Some x -> x
    in
    List.Assoc.add counts line (count + 1)
  )

let (|>) x f = f x ;;

let () =
  build_counts ()
  |> List.sort ~cmp:(fun (_,x) (_,y) -> Int.descending x y)
  |> (fun l -> List.take l 10)
  |> List.iter ~f:(fun (line,count) -> printf "%3d: %s\n" count line)

  (* What's this syntax ?  *)
  (* And after this, split the requisite function into different files as modules. *)

  