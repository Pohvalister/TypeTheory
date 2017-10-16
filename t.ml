open Hw1;;
open Hw2;;
open Hw3_unify;;

(*peano arithm*)
print_int (int_of_peano (S (S (Z)))); print_string "\n";;

print_int (int_of_peano Z); print_string "\n";;

print_int (int_of_peano (inc (peano_of_int 5))); print_string "\n";;
print_int (int_of_peano (inc (peano_of_int 0))); print_string "\n";;

print_int (int_of_peano (add (peano_of_int 2) (peano_of_int 7))); print_string "\n";;
print_int (int_of_peano (add (peano_of_int (1000)) (peano_of_int 7))); print_string "\n";;

print_int (int_of_peano (sub (peano_of_int 10) (peano_of_int 8))); print_string "\n";;
print_int (int_of_peano (sub (peano_of_int 2) (peano_of_int 4))); print_string "\n";;

print_int (int_of_peano (mul (peano_of_int 5) (peano_of_int 7))); print_string "\n";;
print_int (int_of_peano (mul (peano_of_int 0) (peano_of_int 1))); print_string "\n";;

print_int (int_of_peano (div (peano_of_int 10) (peano_of_int 5))); print_string "\n";;
print_int (int_of_peano (div (peano_of_int 7) (peano_of_int 2))); print_string "\n";;

print_int (int_of_peano (power (peano_of_int 2) (peano_of_int 3))); print_string "\n";;
print_int (int_of_peano (power (peano_of_int 2) (peano_of_int 0))); print_string "\n";;

print_string "\narithmetic_OK\n";;

let rec print_list_int = function
[] -> ()
| h::t -> print_int h ; print_string " " ; print_list_int t;;

(* reverse*)
let l = [1;2;3;4;5;6;7;8;9;10];;
print_list_int l;;
print_list_int (rev l);;

(*merge sort*)
let l1 = [4;3;2;1];;
let l2 = [3;6;0;1;432;2;0;4;0;7;10;0];;
let l3 = [909;66;-33;22;8;1;4;4;2;0];;



print_list_int (merge_sort l1);;
print_list_int (merge_sort l2);;
print_list_int (merge_sort l3);;

print_string "\nlist_OK\n";;

(*lambda parsers *)
print_string (string_of_lambda (lambda_of_string "\\x.\\y.x"));;
print_string (string_of_lambda (lambda_of_string "y x"));;
print_string (string_of_lambda (lambda_of_string "(\\y.x) z"));;
print_string (string_of_lambda (lambda_of_string "z x \\y.(y r)"));;
print_string (string_of_lambda (lambda_of_string "\\aaaaaaa.(xxxxxx dsfdfd)"));;
print_string (string_of_lambda (lambda_of_string "((x)) (((((y)))))"));;
(*print_string (string_of_lambda (lambda_of_string "(("));;*)
let x = App(Var "ad", Abs ("as", Var ("ad")));;
print_string (string_of_lambda x);;

print_string "\nparsings_OK\n";;

(*lambda alpha_equ*)
let test st1 st2 b =
	print_string (string_of_bool (b = (is_alpha_equivalent (lambda_of_string st1) (lambda_of_string st2))));;

test "(x)" "(y)" false;;
test "x y" "x y" true;;
test "\\x.x y" "\\y.y y" false;;
test "(\\x.x)(z)(w)" "(\\y.y)(z)(w)" true;;
test "\\x1.\\x2.\\x3.\\x4.x1 x2 x3 x4" "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4" true;;
test "\\x1.\\x2.\\x3.\\x4.(x1 x2 x3 x4)" "\\y1.\\y2.\\y3.\\y4.(y1 y2 y3 y4)" true;;
test "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4" "\\x1.\\x2.\\x3.\\x4.(x4 x2 x3 x1)" false;;
test "\\x1.\\x2.x1 x2" "\\y1.\\y2.y2 y1" false;;

print_string "\nalpha_equ_OK\n";;

let rec print_list_string = function
[] -> ()
| h::t -> print_string h ; print_string " " ; print_list_string t;;

(* free_vars*)
print_list_string ( free_vars (lambda_of_string "\\x.\\y.x"));;
print_list_string ( free_vars (lambda_of_string "y x"));;
print_list_string ( free_vars (lambda_of_string "(\\y.x) z"));;
print_list_string ( free_vars (lambda_of_string "z x \\y.(y r)"));;
print_list_string ( free_vars (lambda_of_string "\\aaaaaaa.(xxxxxx dsfdfd)"));;
print_list_string ( free_vars (lambda_of_string "((x)) (((((y)))))"));;



print_string "\nfree_vars_OK\n";;

(*free_subst*)
let test st1 st2 diff b =
	print_string (string_of_bool (b = (free_to_subst (lambda_of_string st1) (lambda_of_string st2) diff)));;

test "x" "\\x.y" "y" false;;
test "x" "\\x.x" "y" true;;
test "x" "(x) (\\x.y)" "y" false;;
test "x y \\z.z" "\\y.a" "a" false;;
test "x y \\z.z" "\\z.a" "a" true;;
test "x y \\z.z" "\\x.b" "a" true;;
test "x y \\z.z" "\\x.b a" "a" false;;
test "x y \\z.z" "(\\x.b) a" "a" true;;

print_string "\nsubst_OK\n";;

(*norm_form*)
let test st1 b =
	print_string (string_of_bool (b = (is_normal_form (lambda_of_string st1))));;

test "\\x.x y" true;;
test "(\\x.x) y" false;;

print_string "\nKirills tests\n"

let test_free_vars () =
	let test_all f =
		let tests = [
			"\\x.y";
			"\\x.x";
			"(\\x.x x) \\y.y y";
			"(\\x.x x) \\y.y y z";
			"((((((((\\x.\\y.\\x.y)(\\x.x)(\\x.x)(\\a.y)b)))))))";
			"(\\x.x)\\y.x";
			"(\\x.x)(\\z.y)"
		] in
		let rec ta l = match l with
			| hd :: tl -> f hd; ta tl
			| [] -> print_string "Done\n"; print_newline()
		in
		ta tests
	in
	let print_list l =
		let rec pl l =
			match l with
				| head :: tail -> print_string head; print_string ","; pl tail
				| [] -> print_char '}'; print_newline()
		in
		print_char '{';
		pl l
	in
	let go str =
		let a = free_vars (lambda_of_string str) in
		print_list a
	in
	test_all go
;;

let test_free_to_subst () =
	let go term l str =
		if free_to_subst (lambda_of_string term) (lambda_of_string l) str then print_string "True\n"
		else print_string "False\n"
	in
	go "y" "\\x.y" "y";
	go "x" "\\x.y" "y";
	go "x" "\\x.y" "z";
	go "x" "\\x.x" "x";
	go "x" "\\z.x" "x";
	go "x" "(\\x.x) \\z.x" "x";
	go "\\x.x" "\\x.x" "x";
	go "\\y.x" "\\x.x" "x";
	go "\\x.\\x.\\y.y" "\\x.x" "x";
	go "\\x.\\x.\\y.y" "\\x.x" "zzzzzzzzz";
	go "p" "\\x.y" "x"
;;

let test_is_alpha_equivalent () =
	let go s1 s2 =
		if is_alpha_equivalent (lambda_of_string s1) (lambda_of_string s2) then print_string "True\n"
		else print_string "False\n"
	in
	go "x" "y";
	go "y" "y";
	go "abc" "abc";
	go "abc" "abcd";
	go "\\x.x" "\\x.x";
	go "\\x.x" "\\y.y";
	go "\\x.x" "x x";
	go "\\x.y" "\\x.z";
	go "(\\x.y)" "(\\xxx.y)";
	go "(\\x.y) (\\xx.y)" "(\\xxx.y) (\\xx.y)";
	go "(\\x.y) (\\xx.y) (\\xxx.yyy)" "(\\xxx.y) (\\xx.y) (\\x.yyy)";;

let tests_for_reduction_1 = [
	"x";
	"\\x.y";
	"\\x.x";
	"(\\x.x)(\\z.y)";
	"(\\x.(\\x.x) (\\x.x)) (\\y.z)";
	"(\\f.\\x.f (f (f (f x)))) (\\f.\\x.f (f (f (f x))))";
	"(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";
	"(\\x.x x x) (\\x.x) (\\x.x)"
(* 	"(\\x.x x) \\y.y y";
	"(\\x.x x) \\y.y y z";
	"((((((((\\x.\\y.\\x.y)(\\x.x)(\\x.x)(\\a.y)b)))))))";
	"(\\x.x)\\y.x";
	"x";
	"\\x.x";
	"(\\x.x) y";
	"(\\x.\\y.x) y";
	"x x x x x x x xxxxxxxxx";
	"(\\x.x x) \\x.x x";
	"(\\a.b) x";
	"\\y.(\\a.b) x";
	"(\\x.\\y.(\\a.b) x) y";
	"(\\x.\\y.(\\a.\\x.a) x) y";
	"(\\x.y) (\\xx.y) (\\xxx.yyy)";
	"((\\x.(x) (x))) ((\\x.(x) (x)))" *)
];;

let tests_for_reduction_2 = [
	"x";
	"\\x.y";
	"\\x.x";
	"(\\x.x)(\\z.y)";
	"(\\x.(\\x.x) (\\x.x)) (\\y.z)";
	"(\\f.\\x.f (f (f (f x)))) (\\f.\\x.f (f (f (f x))))";
	"(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";
	"(\\x.x x x) (\\x.x) (\\x.x)";
	"((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";
	"\\a.\\b.a (a (a (a (a (a (a (a (a b))))))))"
];;

let test_reduction tests f =
	let apply f t =
		f t;
		print_string " for test: ";
		print_string t;
		print_newline()
	in
	let rec ta l = match l with
		| hd :: tl -> apply f hd; ta tl
		| [] -> print_string "Done\n"; print_newline()
	in
	ta tests;;

let test_is_normal_form () =
	let go str =
		let a = lambda_of_string str in
		if is_normal_form a then print_string "True"
		else print_string "False"
	in
	test_reduction tests_for_reduction_1 go;;

let test_normal_beta_reduction () =
	let go str =
		let a = lambda_of_string str in
		let reduced_l = normal_beta_reduction a in
		let str2 = string_of_lambda reduced_l in print_string str2
	in
	test_reduction tests_for_reduction_1 go;;

let test_reduce_to_normal_form () =
	let go str =
		let a = lambda_of_string str in
		let reduced_l = reduce_to_normal_form a in
		let is_done = is_normal_form reduced_l in
		let str2 = string_of_lambda reduced_l in
		match is_done with
			| true -> print_string str2
			| false -> print_string "NOT NORMAL FORM!!! "; print_string str2
	in
	test_reduction tests_for_reduction_2 go;;

(* test_normal_beta_reduction ();; *)
test_reduce_to_normal_form();;
(* test_is_alpha_equivalent();; *)
print_string "\nKirils_testN2\n"
open List;;

let term_to_string a =
	let rec dfs x =
		match x with
			| Var (var_name) -> var_name
			| Fun (fun_name, arguments) -> "(" ^ fun_name ^
			(List.fold_left (fun prv term ->  prv ^ " " ^ (dfs term)) "" arguments) ^ ")"
	in
	dfs a;;


(* (F x) *)
let term1 = Fun ("F", [Var "x"]);;

(* (F (f a b c) (f e d c)) *)
let term2 = Fun ("F", [(Fun ("f", [(Var "a"); (Var "b"); (Var "c")])); (Fun ("f", [(Var "e"); (Var "d"); (Var "c")]))]);;

(* (F (f a b c) (f e d f) (G (G (g (H (h a b c) (h e d c)) b c)) (g e d f)) ) *)
let term3 = Fun ("F", [Fun("f", [Var "a"; Var "b"; Var "c"]); Fun("f", [Var "e"; Var "d"; Var "c"]);
Fun ("G", [Fun("G", [
Fun ("g", [Fun ("H", [Fun("h", [Var "a"; Var "b"; Var "c"]);Fun("h", [Var "e"; Var "d"; Var "c"])]); Var "b"; Var "c"])
]) ;Fun ("g", [Var "e"; Var "d"; Var "f"])])
]);;

let f () =
	let go aterm =
		let str = term_to_string aterm in
		print_string str;
		print_newline ()
	in
	go (Var "x");
	go term1;
	go term2;
	go term3;;

let test_system_to_eq () =
	let go a =
		let (ans_left, ans_right) = system_to_equation a in
		let (ans_left_str, ans_right_str) = (term_to_string ans_left, term_to_string ans_right) in
		print_string ans_left_str;
		print_string " = ";
		print_string ans_right_str;
		print_newline()
	in
	let system1 = [(term1, term2)] in
	let system2 = [(Var "x", Var "y")] in
	let system3 = [(term1, term2); (Var "x", Var "y"); (term2, term3); (term1, term3)] in
	go system1;
	go system2;
	go system3;;

let rec print_subst s =
	match s with
		| hd :: tl ->
			let (x, y) = hd in
			print_string (x ^ " -> " ^ (term_to_string y) ^ ", ");
			print_subst tl
		| [] -> print_string ";"
;;

let test_apply_substitution () =
	let go subst a =
		let new_term = apply_substitution subst a in
		let str_a = term_to_string a in
		let str = term_to_string new_term in
		print_string str;
		print_string " for test: ";
		print_string (str_a ^ " with subst: ");
		print_subst subst;
		print_newline ()
	in
	let subst1 = [("x", term1)] in
	go subst1 term1;
	let subst2 = [("a", term1); ("c", term1)] in
	go subst2 term2
;;

let test_check_solution () =
	let go subst system =
		let ans = check_solution subst system in
		match ans with
			| true -> print_string "True\n"
			| false -> print_string "False\n"
	in
	let system1 = [(term1, (Var "y"))] in
	let sol1 = [("y", term1)] in
	let sol2 = [("y", term2)] in
	go sol1 system1;
	go sol2 system1;
	let term1 = Fun ("F", [Var "x"; Var "y"]) in
	let sol = [("y", Fun ("f", [Var "e"; Var "d"; Var "c"])); ("x", Fun ("f", [Var "a"; Var "b"; Var "c"]))] in
	let system2 = [(term1, term2)] in
	go sol system2;;

let test_solve_system () =
	let go system =
		let sol = solve_system system in
		match sol with
		| Some x ->
			print_subst x;
			let correct = check_solution x system in
			if correct then print_string " OK\n"
			else print_string " NOT CORRECT!\n"
		| None -> print_string "No solutions\n"
	in
	go [((Var "x"), term2)];
	go [(term2, Var "x")];
	let term1 = Fun ("F", [Fun ("g", [Var "a"; Var "b"]); Var "c"]) in
	let term2 = Fun ("F", [Var "x"; Var "y"]) in
	go [(term1, term2); (term1, term1); (term2, term2)];
	let term1 = Fun ("F", [Fun ("g", [Var "a"; Var "b"]); Var "b"]) in
	let term2 = Fun ("F", [Var "x"; Var "y"]) in
	go [(term1, term2)];
	let sys0 = [(Var "a", Var "b"); (Var "x", Var "y")] in go sys0;
	let sys1 = [(Fun("f",[Var "a"]), Fun("f",[Fun("g",[Fun("h",[Var "b"])])])); (Var "a", Var "b")] in go sys1;
	let sys2 = [(Fun("f",[Var "a"]), Var "b")] in go sys2;
	let sys3 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"])] in go sys3;
	let sys4 = [Fun("f",[Var "a"; Var "b"]), Fun("g",[Var "x"; Var "y"])] in go sys4;
	let sys5 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"; Var "z"])] in go sys5;
	let sys6 = [(Var "a", Fun("f", [Var "a"]))] in go sys6;
	let sys7 = [(Var "a", Var "a")] in go sys7;
	let solvable = [(Fun("f",[Var "x"]), Fun("f",[Fun("g",[Var "y"])])); (Var "y", Fun("h",[Var "p"]))] in go solvable;
	let unsolvable = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h", [Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])]
	in go unsolvable
;;

let test_hashtbl () =
	let tbl = Hashtbl.create 10 in
	let rec f str =
		match str with
			| "xxxxx"-> print_string "All is in hashtbl"; print_newline()
			| "xxxx" -> (Hashtbl.add tbl str (Var "y")); f (str ^ "x")
			| "xxx" -> (Hashtbl.add tbl str term1); f (str ^ "x")
			| "xx" -> (Hashtbl.add tbl str term2); f (str ^ "x")
			| _ -> (Hashtbl.add tbl str term3); f (str ^ "x")
	in
	f "x";
	let solution = Hashtbl.fold (fun k v l -> (k, v) :: l) tbl [] in
	print_subst solution;
	print_newline ()
;;

let test_list () =
	let rec print_list l =
		match l with
		| (Some hd) :: tl -> print_string (hd ^ " "); print_list tl
		| [] -> print_newline()
		| None :: tl -> print_string "None "; print_list tl
	in
	let l = ["a"; "b"; "c"] in
	let f x =
		if x = "b" then None
		else Some x
	in
	let l2 = List.map f l in
	print_list l2
;;

(*f();;*)

(*test_system_to_eq ();;
test_apply_substitution ();;
 test_check_solution ();;*)
test_solve_system ();;
