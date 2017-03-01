open Hw1;;

type lambda = Hw1.lambda;;
let alpha_equ_of x y =
	let rec alpha_equ_supp lam1 lam2 lisx = 
		match (lam1,lam2) with
			(Var v1, Var v2) -> v1=v2 || (List.exists (fun (z, w) -> (z=v1 && w =v2)) lisx)
			|(App (l1, l2), App (l3,l4)) -> ((alpha_equ_supp l1 l3 lisx) && (alpha_equ_supp l2 l4 lisx))
			|(Abs (var1, sen1), Abs (var2, sen2)) -> alpha_equ_supp sen1 sen2 ((var1,var2)::lisx)
			|_ -> false in
	alpha_equ_supp x y [];;

let free_to_add th lam x = 
	let rec get_free_vars l fixed free = 
		let rec my_merge l1 l2 = match l1 with [] -> l2|h::t -> my_merge t (h::l2) in

		match l with
		Var z -> if (not (List.mem z free)) && (not (List.mem z fixed)) then z::free
			else free
		|App(z1, z2) -> my_merge (get_free_vars z1 fixed free) (get_free_vars z2 fixed free)
		|Abs(zStr,z2) -> get_free_vars z2 (zStr::fixed) free in

	let rec check_fixed_in lam point fixed vars = match lam with 
		Var v -> if point = v then (List.exists (fun var -> (List.mem var fixed)) vars)
			else false
		|App (l1, l2) -> (check_fixed_in l1 point fixed vars) || (check_fixed_in l2 point fixed vars)
		|Abs (vStr, l1) -> check_fixed_in l1 point (vStr::fixed) vars in
	not (check_fixed_in lam x [] (get_free_vars th [] []));;
