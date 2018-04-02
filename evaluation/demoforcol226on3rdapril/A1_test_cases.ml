let alphabet=[Constructor '1';Constructor '2';Constructor 'a';Constructor 'b';Constructor 'c';Constructor 'A'];;

let es1 = create "";;
let es2 = create "a";;
let es3 = create "abc";;
let es4 = create "12";;

lgh es1;;
lgh es2;;
lgh es3;;
lgh es4;;
(* lgh "";;
lgh "a";;
lgh "abc";;
lgh "12";; *)

nonempty es1;;
nonempty es2;;
nonempty es4;;
(* nonempty Nil;;
nonempty "a";;
nonempty "12";; *)

concat es1 es1;;
concat es1 es2;;
concat (create "1") es1;;
concat (create "1A") es3;;
(* concat Nil Nil;;
concat Nil "a";;
concat "1" Nil;;
concat "1A" "abc";; *)

reverse es1;;
reverse es3;;
reverse es4;;
(* reverse Nil;;
reverse "abc";;
reverse "12";; *)


(* first es1;; *) 
(* Gives Empty exception ^^ *)
first es2;;
first es3;;
(* first Nil;;
first "a";;
first "abc";; *)

(* last es1;; *)
(* Gives Empty exception ^^ *)
last es2;;
last es3;;
(* last Nil;;
last "a";;
last "abc";; *)

let editable = create "abac12a2aAac211";;

forward editable;;
editable;;
back editable;;
editable;;
moveTo 10 editable ;;
editable;;
replace (Constructor 'b') editable ;;
editable;;

