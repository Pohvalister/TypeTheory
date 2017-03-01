type peano = Z | S of peano;; (* òèïû íåîáõîäèìî êîïèðîâàòü â ðåàëèçàöèþ *)
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x = match x with
  0 -> Z
  |_ -> S(peano_of_int (x - 1));;  

let rec int_of_peano p = match p with
    Z -> 0
  | S x -> 1 + int_of_peano x;;

let inc x = S(x);;

let rec add x y = match y with
  Z -> x
  |S(z) -> inc (add x z);;

let dec x = match x with
  Z -> Z
  |S(z) -> z;;

let rec sub x y = match y with
  Z -> x
  |_ -> sub (dec x) (dec y);;

let rec mul x y = match y with
  Z -> Z
  |S(z) -> add x (mul x z);;

let div x y =
  let rec recDiv c a b = match a with
    Z -> c
    |_ -> recDiv (inc c) (sub a b) b
  in
  (recDiv Z x y);;

let rec power x y = match y with 
  Z -> S(Z)
  |S(z) -> mul x (power x z);;


let rev x =
  let rec revSup from_ to_ = match from_ with
    [] -> to_
    |h::t -> revSup t (h::to_)
  in
  revSup x [];;



let rec listLen x c = match x with
  [] -> c
  |h::t -> listLen t (1 + c);;

let rec divide_list list_ left right len = match len, list_ with
  0, l -> right :=l
|_, h::t -> left :=h::!left; divide_list t left right (len - 1)
|_, _ -> failwith "Something wrong";;

let rec merge x y = match x, y with
[], s -> s
|s, [] -> s
|xh::xt, yh::yt -> if xh < yh
			then xh :: (merge xt y)
			else yh :: (merge yt x);;

let rec merge_sort list_ = match list_ with
[] -> []
|[x] -> [x]
|_ -> 
	(let left = ref [] in
	let right = ref [] in
	divide_list list_ left right ((listLen list_ 0)/2); 
	merge (merge_sort !left) (merge_sort !right));;

                     
let rec string_of_lambda x = match x with
Var x -> x
|App(l1,l2) -> "(" ^ (string_of_lambda l1) ^ " " ^ (string_of_lambda l2) ^ ")"
|Abs(s,l) -> "(\\" ^ s ^ "." ^ (string_of_lambda l) ^ ")";;

let lambda_of_string str = 
	let str = str ^ ";" in 
	let pos = ref 0 in
	let get () = str.[!pos] in
	let next () = if !pos < String.length str - 1 then pos := !pos +1 in
	let eat x = if get () = x then next () else failwith ("Unexpected symbols" ^ (String.make 1 (get())) ^ string_of_int(!pos)) in
	let rec string_eater tmpStr = 
		if (get ()) <>';' && (get ()) <> ')' && (get ()) <> ' ' && (get ())<> '\\' && (get ()) <> '(' && (get ())<> '.' then (
			let current = tmpStr ^ (String.make 1 (get())) in next();
			string_eater current
			)
		else ( 
			tmpStr 
			) in
	let rec parse () = 
		match (get()) with
			'\\' -> parse_abs ()
			|'(' -> (let tmpValue = bracket_parse () in
					if (get()=' ') then (
					eat ' ';
					App(tmpValue, parse())
					)
					else
					tmpValue
				)	
			|_ -> var_or_app_parse ()

	and bracket_parse () = eat '('; let tmp = parse() in eat ')'; tmp

	and parse_abs () = eat '\\';
			let nameStr = string_eater "" in
			eat '.';
			Abs(nameStr, parse())

	and var_or_app_parse () = let nameStr = string_eater "" in
				if (get() = ' ') then begin
					eat ' ';
					App(Var(nameStr), parse())
					end
				else Var(nameStr)
	 in
	parse ();;
