open Hw1;;

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


let l = [1;2;3;4;5;6;7;8;9;10];;
print_list l;;
print_list (rev l);;

let l1 = [4;3;2;1];;
let l2 = [3;6;0;1;432;2;0;4;0;7;10;0];;
let l3 = [909;66;-33;22;8;1;4;4;2;0];;



print_list (merge_sort l1);;
print_list (merge_sort l2);;
print_list (merge_sort l3);;
(*
print_string (Hw1.string_of_lambda (Hw1.lambda_of_string "\\x.\\y.x"));;
*)
