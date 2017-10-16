type algebraic_term = Var of string | Fun of string * (algebraic_term list)

(* at -> string *)
let term_to_string at =
	let rec impl at =
		match at with
			Var v -> v
			| Fun(f, args) -> f ^ "(" ^ (impl_l args) ^ ")"
	and impl_l l =
		match l with
			[] -> ""
			| (h::[]) -> (impl h) (* for last arg no last space *)
			| (h::t) -> (impl h) ^ " " ^ (impl_l t) in
	impl at;;


(* eq -> string *)
let equation_to_string eq =
	let lhs, rhs = eq in
	term_to_string lhs ^ " = " ^ term_to_string rhs;;


(* sys -> string *)
let rec system_to_string sys =
	match sys with
		[] -> ""
		| (h::t) -> (equation_to_string h) ^ "\n" ^ (system_to_string t);;

module StringSet = Set.Make (
struct
	type t = string
	let compare = String.compare
end);;

module StringMap = Map.Make (
struct
	type t = string
	let compare = String.compare
end);;

(*produces unique name from system*)
let gen_unique_name_in system =
	let counter = ref 0 in

	let rec get_names_from lst =
		let rec get_func_names term =
			match term with
			| Var var -> StringSet.empty
			| Fun (str, lst) -> StringSet.add str (get_names_from lst)
		in
		match lst with
		| [] -> StringSet.empty
		| h::t -> StringSet.union (get_func_names h) (get_names_from t)
	in
	let (left_list, right_list) = List.split system in
	let namesList = StringSet.union (get_names_from left_list) (get_names_from right_list) in

	while (StringSet.mem ("unique_"^ string_of_int !counter) namesList )do
		counter := !counter + 1;
	done;
	("unique_"^ string_of_int !counter)
;;

let system_to_equation system =
	let (left_list, right_list) = List.split system in
	let uniqueName = gen_unique_name_in system in
	(Fun(uniqueName, left_list), Fun(uniqueName, right_list))
;;

let apply_substitution subt_list term =
	let rec parse_ subt_list map =
		match subt_list with
		| (var, term)::t -> parse_ t (StringMap.add var term map)
		| [] -> map
	in

	let rec evolve_term term map =
		match term with
		| Var var -> if (StringMap.mem var map)	then StringMap.find var map
												else Var var
		| Fun (str, term_list) -> Fun(str, evolve_term_list term_list map)
	and evolve_term_list term_list map =
		match term_list with
		| h::t -> (evolve_term h map)::(evolve_term_list t map)
		| [] -> []
	in
	evolve_term term (parse_ subt_list StringMap.empty)
;;

let check_solution solut system =
	let rec check_solution_rec solut system =
		let rec equ_struct_of term1 term2 =
			match (term1, term2) with
			 | (Var var1, Var var2) -> var1 = var2
			 | (Fun (name1, list1), Fun (name2,list2)) -> (name1 = name2) && (equ_struct_of_list list1 list2)
			 | _ -> false
		and equ_struct_of_list l1 l2 =
			match (l1, l2) with
			| (h1::t1,h2::t2) -> (equ_struct_of h1 h2) && (equ_struct_of_list t1 t2)
			| ([],[]) -> true
			| _ -> false
		in
		match system with
		| (left, right)::t -> (equ_struct_of (apply_substitution solut left) (apply_substitution solut right)) && (check_solution_rec solut t)
		| [] -> true
	in
	check_solution_rec solut system
;;

exception InvalidSystem
(*----System Solving---*)
let solve_system system =
	let answer_place = ref system in

	(*Unfolding functions in one equality*)
	let rec unfold_funcs old_system new_system_ref =

		let rec connect_lists lst1 lst2 system_ref =
			match (lst1,lst2) with
			| (term1::tail1, term2::tail2) -> connect_lists tail1 tail2 system_ref;system_ref:=(term1,term2)::!system_ref
			| ([], []) -> ()
		in

		let rec try_unfold equ =
			match equ with
			(*T=T => delete same*)
			(*T=F => lists needed to be solved*)
			| (Fun(name1, lst1), Fun(name2,lst2)) -> if (name1 = name2 && lst1 = lst2) then false
																																								else
																																								(if (name1 = name2 && List.length lst1 = List.length lst2)	then (connect_lists lst1 lst2 new_system_ref; true)
																																																																						else raise InvalidSystem
																																								)
			| expr -> new_system_ref:=expr::!new_system_ref;false
		in

		match old_system with
		[] -> new_system_ref:=[];false
		| equ::tail -> (unfold_funcs tail new_system_ref) || (try_unfold equ)
	in

	(*T=x, T is not var => x=T*)
	let rec reverse_final_equ old_system new_system_ref =
		match old_system with
		[] -> new_system_ref := []
		| equ::tail ->	reverse_final_equ tail new_system_ref;(
																													match equ with
																													| (Fun(name, lst),Var var) -> new_system_ref := (Var var,Fun(name,lst))::(!new_system_ref)
																													| expr -> new_system_ref := expr::!new_system_ref
																													)
	in

	(*Unfolding functions in diff equalities
	x=T, R=S, x is in R or S => x=T; R[x:=T]=S[x:=T];*)
	let insert_funcs old_system new_system_ref =

		let frstSystem = ref old_system in
		let scndSystem = ref [] in
		(*ищет переменную которую можно подставить (есть хотя бы одно место) - если есть - подставляет и true, иначе false*)
		let rec find_vars cur_system whole_system evolved_system_ref =
			(*если equ - Var = Term, то пытается поставить Term вместо Var в from_system, записывая по ссылку to_system_ref - возвращ была ли подстановка*)
			let evolve equ from_system to_system_ref =
				(*рекурсивно спускается и выполняет insert_var для каждого equ*)
				let rec insert_var var term from_system to_system_ref =
					(*подставляет терм в терм - возвращ пару - была ли подстановка; новый терм*)
					let rec try_to_subst var what_term to_term =
						match to_term with
						| Fun(name, lst) ->let answer_list = List.map (fun x -> try_to_subst var what_term x) lst in ((List.fold_left (fun acc x -> acc || (fst x)) false answer_list), Fun (name, (List.map (fun x -> snd x) answer_list)))
						| Var x -> if (x=var) then (true, what_term) else (false, to_term)

					(*подставляет терм в систему, записывая новую по ссылке - возвращ была ли подстановка*)
					and insert var term left_term right_term =

						let (subst_answ1,subst_answ2)  = (try_to_subst var term left_term, try_to_subst var term right_term) in

						if ((fst subst_answ1) || (fst subst_answ2)) then (to_system_ref:=((snd subst_answ1), (snd subst_answ2))::!to_system_ref; true)
																	else (to_system_ref:=((snd subst_answ1), (snd subst_answ2))::!to_system_ref; false)
					in

					let is_var term =
						match term with
						Var var -> true
						|_ -> false
					in

					match from_system with
					[] -> false
					| (left_term,right_term)::tail ->	(if ((is_var left_term) && (fst (try_to_subst var term right_term)))	then raise InvalidSystem
																														else (insert var term left_term right_term) && (insert_var var term tail to_system_ref)
														)
				in

				match equ with
				| (Var var, Var var1) -> false (*x=x - бесполезно*)
				| (Var var, term) -> insert_var var term from_system to_system_ref
				| _ -> false
			in

			match cur_system with
			| [] -> false
			| equ::tail -> if (evolve equ whole_system evolved_system_ref)	then true
																			else (evolved_system_ref:=[]; find_vars tail whole_system evolved_system_ref)
		in
		(* крутится в цикле находя новые переменые и пытаясь подставить их в остальные термы*)
		let useful_work_flag = ref (find_vars !frstSystem !frstSystem scndSystem) in
		if (not !useful_work_flag)	then false
										else (
											frstSystem:= [];
												while (find_vars !scndSystem !scndSystem frstSystem) do
													scndSystem:= [];
													find_vars !frstSystem !frstSystem scndSystem;
													frstSystem:= [];
												done;
												new_system_ref:= !frstSystem;
												true
											)
	in
	(*цикл последовательных операций - 1)удалить одинаковые, 2)раскрыть равенства, 3)развернуть термы переменной влево 4)подставить все возможные Var x = term друг в друга*)

	let useful_work_flag = ref true in
	while !useful_work_flag do
		while (unfold_funcs !answer_place answer_place) do
		();
		done;
		reverse_final_equ !answer_place answer_place;
		(*print_string (system_to_string !answer_place);*)
		useful_work_flag := insert_funcs !answer_place answer_place;
	done;

	let rec get_answer ans_place =
		match ans_place with
		(Var var, term)::tail -> let tmp = get_answer tail in ((fst tmp),(var,term)::(snd tmp))
		| [] -> (true,[])
		| _ -> (false, [])
	in
	let tmp = get_answer !answer_place in if ((fst tmp))then Some (snd tmp)
																											else None
;;
