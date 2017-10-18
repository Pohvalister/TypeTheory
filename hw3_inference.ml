module StringSet = Set.Make(String)
module StringMap = Map.Make(String)


type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type;;
type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

exception BadSolvingException of string;;(*code problems*)

let infer_simp_type lam =(*lambda -> ((string * simp_type list) * simp_type)*)

	let counter= ref 1 in
	let gen_var () =
		counter:= !counter + 1;
		"α1" ^ string_of_int !counter
	in

	let rec get_types lam types_map =  (*lambda -> Map : string * S_Elem -> (List : (simp_type simp_type),simp_type)*)
		match lam with
		| Hw1.Var var  -> ([], StringMap.find var types_map)
		| Hw1.App (lam1, lam2) ->	let (map1, type1), (map2, type2) = (get_types lam1 types_map), (get_types lam2 types_map) in
								let new_type = S_Elem(gen_var()) in
								(List.append map1 (List.append map2 [(type1,S_Arrow(type2, new_type))]), new_type)
		| Hw1.Abs (var, lam) -> let new_map = StringMap.add var (S_Elem (gen_var())) types_map in
							let map, type1 = get_types lam new_map in
							(map, S_Arrow(StringMap. find var new_map, type1))
	in

	let rec simple_to_algebraic st = (*simp_type -> algebraic_term*)
		match st with
		| S_Elem elem  -> Hw3_unify.Var elem
		| S_Arrow (type1, type2) -> Hw3_unify.Fun("myFunc", [simple_to_algebraic type1; simple_to_algebraic type2])
	in

	let simple_to_algebraic_in_list lst = (*List: simp_type -> List : algebraic_term*)
		List.map (fun (left, right) -> ((simple_to_algebraic left), (simple_to_algebraic right))) lst
	in

	let rec algebraic_to_simple at = (*algebraic_term -> simp_type*)
		match at with
		| Hw3_unify.Var var-> S_Elem var
		| Hw3_unify.Fun (name, [left;right](*because came from st*)) -> S_Arrow (algebraic_to_simple left, algebraic_to_simple right)
		| _ -> raise (BadSolvingException "Can't alg term to simp_type - bad arguments value")
	in

	let algebraic_to_simple_in_list lst = (*List : algebraic_term -> List : simp_type*)
		List.map (fun (var, at)-> (var, algebraic_to_simple at)) lst
	in

	let rec assosiate varLst map =(*List : string -> Map : string * simp_type -> Map : string * simp_type*)
		match varLst with
		| h::t -> assosiate t (StringMap.add h (S_Elem(gen_var ())) map)
		| [] -> map
	in

	let free_vars_map = assosiate (Hw2.free_vars lam) StringMap.empty in
	let types_system, result_type = get_types lam free_vars_map in

	match Hw3_unify.solve_system (simple_to_algebraic_in_list types_system) with
	| None -> None
	| Some solution -> Some (algebraic_to_simple_in_list solution, algebraic_to_simple (Hw3_unify.apply_substitution solution (simple_to_algebraic result_type)))
;;

exception BadSystemException of string;;

let algorithm_w lamHM = (* hm_lambda -> ((string * hm_type list ) * hm_type) optional*)

	let counter= ref 0 in
	let gen_var () =
		counter:= !counter + 1;
		"α2" ^ string_of_int !counter
	in

	let rec cycling lamHM cycleTypes =(*hm_lambda -> Map : string * hm_type -> (Map : string * hm_type,hm_type)*)

		(*------Useful functions------*)

		let apply_subst subst typeHM = (*Map: string * hm_type -> hm_type -> hm_type*)

			let rec apply_subst_rec typeHM set(*blocked*) = (*hm_type -> Set: string -> hm_type*)
				match typeHM with
				| HM_Elem var -> if StringSet.mem var set	then typeHM
															else if StringMap.mem var subst	then StringMap.find var subst
																							else typeHM
				| HM_Arrow (typeHM_1, typeHM_2) -> HM_Arrow(apply_subst_rec typeHM_1 set, apply_subst_rec typeHM_2 set)
				| HM_ForAll (var, typeHM)-> HM_ForAll (var, apply_subst_rec typeHM (StringSet.add var set))
			in

			apply_subst_rec typeHM StringSet.empty
		in

		let apply_subst_in_map subst map1 = (*Map : string * hm_type -> Map : string * hm_type -> Map : string * hm_type *)
			StringMap.fold (fun place type1 map -> (StringMap.add place (apply_subst subst type1) map)) map1 StringMap.empty
		in

		let merge_subst typeMap2 typeMap1 = (*Map: string * hm_type -> Map: string * hm_type -> Map: string * hm_type*)
			StringMap.fold (fun place type1 map -> if StringMap.mem place map then map else StringMap.add place type1 map) typeMap2 (StringMap.fold (fun place type1 map -> StringMap.add place (apply_subst typeMap2 type1) map) typeMap1 StringMap.empty)
		in

		(*------Case_1------*)
		let var_case varHM = (*String -> (Map : string * hm_type, hm_type) *)

			let rec unfold typeHM =(*hm_type -> hm_type*)
				match typeHM with
				| HM_ForAll(str, typeHM) -> (apply_subst (StringMap.singleton str (HM_Elem(gen_var ()))) (unfold typeHM))
				| _ -> typeHM
			in

			if (StringMap.mem varHM cycleTypes)	then (StringMap.empty,  unfold (StringMap.find varHM cycleTypes))
												else raise (BadSystemException "Variables are not free")
		in

		(*------Case_2------*)
		let app_case lamHM1 lamHM2  = (*hm_lambda -> hm_lambda -> (Map : string * hm_type, hm_type) *)
			let (typeMap1, type1), (typeMap2, type2) = (cycling lamHM1 cycleTypes), (cycling lamHM2 cycleTypes) in (*!!!!!*)
			let fresh = gen_var() in

			let rec hmt_to_algt hmt = (*hm_type -> algebraic_term*)
				match hmt with
				| HM_Elem var -> Hw3_unify.Var var
				| HM_Arrow(typeHM_1, typeHM_2) -> Hw3_unify.Fun("myFun", [hmt_to_algt typeHM_1; hmt_to_algt typeHM_2])
				| _ -> raise (BadSolvingException "Can't convert hm_type to alg term")
			in

			let convert_system_algt_hmt atSystem = (*List: string * algebraic_term -> Map : string * hm_type*)

				let rec algt_to_hmt at = (*algebraic_term -> hm_type*)
					match at with
					|Hw3_unify.Var var -> HM_Elem var
					|Hw3_unify.Fun("myFun", [x;y]) -> HM_Arrow (algt_to_hmt x, algt_to_hmt y)
					| _ -> raise (BadSolvingException "Can't convert alg term tp hm_type - strange func name")
				in

				List.fold_left(fun map (var, at) -> StringMap.add var (algt_to_hmt at) map) StringMap.empty atSystem(*!!!*)
			in

			let resultSystem = Hw3_unify.solve_system [hmt_to_algt (apply_subst typeMap2 type1), hmt_to_algt (HM_Arrow(type2(*!!!!*), HM_Elem(fresh)))] in

			match resultSystem with(*(string * algebraic_term) list *)
			| None -> raise (BadSystemException "Type Unification failed")
			| Some res ->	let unif_subst =  convert_system_algt_hmt res in
							let merged = merge_subst unif_subst (merge_subst typeMap2 typeMap1) in
							(merged, apply_subst merged (HM_Elem fresh))
		in

		(*------Case_3------*)
		let abs_case str lamHM = (*string -> hm_lambda -> (Map : string * hm_type, hm_type) *)
			let fresh = gen_var() in
			let tmpMap = StringMap.remove str cycleTypes in let tmpMap = StringMap.add str (HM_Elem(fresh)) tmpMap in
			let map, typeHM = cycling lamHM tmpMap in
			(map, HM_Arrow((apply_subst map (HM_Elem(fresh))),typeHM))
		in

		(*------Case_4------*)
		let let_case str lamHM1 lamHM2 = (*string -> hm_lambda -> hm_lambda -> (MAp: string * hm_type, hm_type) *)

			let closure typeHM map = (* hm_type -> (Map : string * hm_type, hm_type) -> hm_type*)

				let free_vars_of_typeHM typeHM =(*hm_type -> Set : string *)

					let rec rec_free_vars typeHM blockedSet = (*hm_type -> Set: string -> Set: string*)
						match typeHM with
						| HM_Elem var -> if (StringSet.mem var blockedSet)	then StringSet.empty
																			else StringSet.singleton var
						| HM_Arrow (typeHM_1,typeHM_2) -> StringSet.union (rec_free_vars typeHM_1 blockedSet) (rec_free_vars typeHM_2 blockedSet)
						| HM_ForAll (var, typeHM) -> rec_free_vars typeHM (StringSet.add var blockedSet)
					in

					rec_free_vars typeHM StringSet.empty
				in

				let map_free_vars = StringMap.fold (fun k v set -> StringSet.union (free_vars_of_typeHM v) set) map StringSet.empty in
				let thm_free_vars = free_vars_of_typeHM typeHM in
				StringSet.fold (fun k t -> HM_ForAll(k,t)) (StringSet.fold(fun k set -> if StringSet.mem k map_free_vars then set else StringSet.add k set) thm_free_vars StringSet.empty) typeHM
			in

			let map1, typeHM_1 = cycling lamHM1 cycleTypes in
			let tmpMap = apply_subst_in_map map1 cycleTypes in
			let tmpMap2 = StringMap.remove str tmpMap in
			let tmpMap2 = StringMap.add str (closure typeHM_1 tmpMap) tmpMap2 in
			let map2, typeHM_2 = cycling lamHM2 tmpMap2 in
			(merge_subst map2 map1, typeHM_2)
		in

		(*------Core------*)
		match lamHM with
		| HM_Var (varHM) -> var_case varHM
		| HM_App (lamHM1,lamHM2)-> app_case lamHM1 lamHM2
		| HM_Abs (str,lamHM)-> abs_case str lamHM
		| HM_Let (str,lamHM_S,lamHM_A) -> let_case str lamHM_S lamHM_A
	in


	let rec lhm_free_vars lamHM setBlocked =
		match lamHM with
		| HM_Var var -> if StringSet.mem var setBlocked then StringSet.empty else StringSet.singleton var
		| HM_Abs(var, lamHM) -> lhm_free_vars lamHM (StringSet.add var setBlocked)
		| HM_Let(var, lamHM1, lamHM2) -> StringSet.union (lhm_free_vars lamHM1 setBlocked) (lhm_free_vars lamHM2 (StringSet.add var setBlocked))
		| HM_App(lamHM1, lamHM2) -> StringSet.union (lhm_free_vars lamHM1 setBlocked) (lhm_free_vars lamHM2 setBlocked)
	in

	let free_vars = lhm_free_vars lamHM StringSet.empty in
	let primary_map = StringSet.fold (fun var map -> StringMap.add var (HM_Elem(gen_var ())) map) free_vars StringMap.empty in

	try
		let (answerMap, answerType) = cycling lamHM primary_map in
		Some ((StringMap.bindings answerMap), answerType)
	with (BadSystemException message) -> None
;;
