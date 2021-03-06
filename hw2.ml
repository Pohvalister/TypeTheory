open Hw1;;

module StringMap = Map.Make (String);;
module StringSet = Set.Make (String);;


let free_vars lam =
	let rec free_vars_rec lam = 
		match lam with 
		Var x  ->  StringSet.add x StringSet.empty 
		| App (lam1, lam2) -> StringSet.union (free_vars_rec lam1) (free_vars_rec lam2)
		| Abs (var, lam) -> StringSet.remove var (free_vars_rec lam)
	in
	StringSet.elements (free_vars_rec lam)
;;

let free_to_subst rePl lam var =
	let rePl_vars = StringSet.of_list (free_vars rePl) in

	(*checking from bottom: 1 - exists, but OK; 0 - doesn't exists; -1 - exists and broken *)
	let rec is_free lam=
		match lam with
		Var place -> if (place = var) then 1 else 0
		| App(lam1, lam2) -> let tmp1, tmp2 = (is_free lam1), (is_free lam2) in (if ((tmp1 = -1)|| (tmp2 = -1))	then -1
																											else if (tmp1 = 1 || tmp2 = 1)	then 1
																																			else 0)
		| Abs(var1, lam) -> let tmp = is_free(lam) in if (var1=var || tmp=0) then 0 else if (tmp = -1 ||(tmp=1 && StringSet.mem var1 rePl_vars)) then -1 else 1
	in
	(is_free lam) <> -1(* free_to_subst x \\x.x y ==false ????*)
;;
(*let free_to_subst th lam x = 
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
*)


let is_alpha_equivalent lam1 lam2 = 
	let uniqueVar = ref "" in
		
	let rec is_alpha_equivalent_rec lam1 map1 lam2 map2 =
		let renew_unique = 
			uniqueVar := !uniqueVar ^ "0";
			!uniqueVar
		in

		let evolve var map =
			if (StringMap.mem var map)	then (StringMap.find var map)
										else var
		in

		let update map oldVar newVar =
			if (StringMap.mem oldVar map)	then map
											else StringMap.add oldVar newVar map
		in

		match (lam1,lam2) with
		(Var var1, Var var2) -> ((evolve var1 map1) = (evolve var2 map2))
		|(App (lam11, lam12), App(lam21,lam22)) -> ((is_alpha_equivalent_rec lam11 map1 lam21 map2) && (is_alpha_equivalent_rec lam12 map1 lam22 map2))
		|(Abs (var1, lam1), Abs (var2, lam2)) -> let change = renew_unique in is_alpha_equivalent_rec lam1 (update map1 var1 change) lam2 (update map2 var2 change)
		| _ -> false
	in

	uniqueVar:= (Hw1.string_of_lambda lam1)^(Hw1.string_of_lambda lam2);
	is_alpha_equivalent_rec lam1 StringMap.empty lam2 StringMap.empty
;;


let is_normal_form lam =
	let rec is_normal_form_rec lam =
		match lam with
			Var v -> true
			|App (Abs (var,lam1),lam2) -> false
			|App (lam1, lam2) -> (is_normal_form_rec lam1) && (is_normal_form_rec lam2)
			|Abs (var, lam) -> is_normal_form_rec lam in
	is_normal_form_rec lam

;;

let rename_arguments lam =
	let counter = ref 0 in
	let gen_var () = 
		counter:= !counter + 1;
		"α" ^ string_of_int !counter
	in 

	let rec rename lam map =
		match lam with
		| Var var -> if (StringMap.mem var map) then (Var (StringMap.find var map)) else Var(var)
		| Abs (var, lam) -> let tmp = gen_var() in Abs(tmp, rename lam (StringMap.add var tmp map))
		| App (lam1, lam2) -> App(rename lam1 map, rename lam2 map)
	in

	rename lam StringMap.empty
;;

let normal_beta_reduction lam =
	let renamedLam = rename_arguments lam in
	let answer = ref renamedLam in

	(*searches recursive for first place to insert - returns true when found; !answer - changed value*)
	let rec search lam = 
		let rec insert lam place rePl = 
			match lam with
			Var var -> if (place = var)	then rePl
										else lam
			| Abs(var, lam1) -> if (place = var)	then lam1
													else Abs(var,(insert lam1 place rePl))
			| App(lam1, lam2) -> App ((insert lam1 place rePl), (insert lam2 place rePl))
		in

		match lam with
		Var var -> false
		| App(Abs(var,lam1), lam2) -> if (free_to_subst lam2 lam1 var)	then (answer:= (insert lam1 var lam2); true)
																		else if (search (Abs(var, lam1)))	then (answer:= App(!answer, lam2);true)
																											else if (search lam2)	then (answer:=App(Abs(var,lam1),!answer);true)
																																	else false
		| App(lam1, lam2) -> if (search lam1)	then (answer:=App(!answer,lam2);true)
												else if (search lam2)	then (answer:=App(lam1,!answer);true)
																		else false
		| Abs(var,lam) -> if (search lam)	then (answer:=Abs(var,!answer);true)
											else false
	in
	if (search renamedLam) then !answer else lam
;;


type lambda_shared = Var_Sh of string | Abs_Sh of string * lambda_shared ref | App_Sh of lambda_shared ref * lambda_shared ref;;

let reduce_to_normal_form lam1 =
	(* converting to memomised lam and to usual*)
	let rec convert_to_sh lam = 
		match lam with
		Var var -> ref (Var_Sh var)
		| Abs(var,lam) -> ref (Abs_Sh(var, (convert_to_sh lam)))
		| App(lam1,lam2) -> ref (App_Sh((convert_to_sh lam1), (convert_to_sh lam2)))
	in

	let rec convert_to_norm lamSh = 
		match !lamSh with
		Var_Sh varSh -> Var varSh
		|Abs_Sh(varSh,lamSh) -> Abs (varSh, convert_to_norm lamSh)
		|App_Sh(lamSh1,lamSh2) -> App (convert_to_norm lamSh1, convert_to_norm lamSh2)
	in
	(*\converting to memomised lam and to usual*)

	let rec reduce_in_shared_form lamSh =

		let free_to_subst_in_shared rePl lamSh var=
			free_to_subst (convert_to_norm rePl) (convert_to_norm lamSh) var
		in

		let rec insert_shared lamSh placeSh replSh = 
			match !lamSh with
			Var_Sh varSh -> if (placeSh = varSh) then lamSh:=!replSh
			|Abs_Sh(varSh,lamSh) -> if (not (placeSh = varSh)) then (insert_shared lamSh placeSh replSh)
			|App_Sh(lamSh1,lamSh2) -> (insert_shared lamSh1 placeSh replSh); (insert_shared lamSh2 placeSh replSh)
		in

		let rec copy_shared lamSh = 
			match !lamSh with
			Var_Sh var -> ref (Var_Sh var)
			| Abs_Sh(varSh,lamSh) -> ref (Abs_Sh(varSh, (copy_shared lamSh)))
			| App_Sh(lamSh1,lamSh2) -> ref (App_Sh(copy_shared lamSh1, copy_shared lamSh2))
		in

		(*cycling will reduce lam from current, when true - cycling is ended, false - maybe require cycling one more time*)
		let rec cycling lamSh =
			match !lamSh with
			Var_Sh varSh -> true
			| Abs_Sh(varSh,lamSh) -> cycling lamSh
			| App_Sh(lamSh3,lamSh2) ->	(match !lamSh3 with
										 Abs_Sh(varSh, lamSh1) -> if (free_to_subst_in_shared lamSh2 lamSh1 varSh) then (lamSh:= !(copy_shared lamSh1); insert_shared lamSh varSh lamSh2;false)
																													else if (not (cycling lamSh3))	then (cycling lamSh)
																																					else if (not (cycling lamSh2))	then (cycling lamSh)
																																													else true 
										| _ -> if (not (cycling lamSh3))	then (cycling lamSh)
																			else if (not (cycling lamSh2))	then (cycling lamSh)
																											else true  
										)
		in
		if (cycling lamSh)	then lamSh
							else (reduce_in_shared_form lamSh) (*run new cycling*)
	in

	convert_to_norm (reduce_in_shared_form (convert_to_sh (rename_arguments lam1)))
;;