open Hw1;;
open Hw2;;

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


let rec print_list = function 
[] -> ()
| h::t -> print_int h ; print_string " " ; print_list t;;

(* reverse*)
let l = [1;2;3;4;5;6;7;8;9;10];;
print_list l;;
print_list (rev l);;

(*merge sort*)
let l1 = [4;3;2;1];;
let l2 = [3;6;0;1;432;2;0;4;0;7;10;0];;
let l3 = [909;66;-33;22;8;1;4;4;2;0];;



print_list (merge_sort l1);;
print_list (merge_sort l2);;
print_list (merge_sort l3);;

(*lambda parsers *)
print_string (string_of_lambda (lambda_of_string "\\x.\\y.x"));;
print_string (string_of_lambda (lambda_of_string "y x"));;
print_string (string_of_lambda (lambda_of_string "(\\y.x) z"));;
print_string (string_of_lambda (lambda_of_string "z x \\y.(y r)"));;
print_string (string_of_lambda (lambda_of_string "\\aaaaaaa.(xxxxxx dsfdfd)"));;
print_string (string_of_lambda (lambda_of_string "((x)) (((((y)))))"));;
print_string (string_of_lambda (lambda_of_string "(("));;
let x = App(Var "ad", Abs ("as", Var ("ad")));;
print_string (string_of_lambda x);;

(*lambda alpha_equ*)
let test st1 st2 b = 
	print_string (string_of_bool (b = (alpha_equ_of (lambda_of_string st1) (lambda_of_string st2))));;

test "(x)" "(y)" false;;
test "x y" "x y" true;;
test "\\x.x y" "\\y.y y";;
test "(\\x.x)(z)(w)" "(\\y.y)(z)(w)" true;;
test "\\x1.\\x2.\\x3.\\x4.x1 x2 x3 x4" "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4" true;;
test "\\x1.\\x2.\\x3.\\x4.(x1 x2 x3 x4)" "\\y1.\\y2.\\y3.\\y4.(y1 y2 y3 y4)" true;;
test "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4" "\\x1.\\x2.\\x3.\\x4.(x4 x2 x3 x1)" false;;
test "\\x1.\\x2.x1 x2" "\\y1.\\y2.y2 y1" false;;

(*free_subst*)
let test st1 st2 diff b =
	print_string (string_of_bool (b = (free_to_add (lambda_of_string st1) (lambda_of_string st2) diff)));;

test "x" "\\x.y" "y" false;;
test "x" "\\x.x" "y" true;;
test "x" "(x) (\\x.y)" "y" false;;
test "x y \\z.z" "\\y.a" "a" false;;
test "x y \\z.z" "\\z.a" "a" true;;
test "x y \\z.z" "\\x.b" "a" true;;
test "x y \\z.z" "\\x.b a" "a" false;;
test "x y \\z.z" "(\\x.b) a" "a" true;;

