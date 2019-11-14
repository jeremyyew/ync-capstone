let rec traced_fac_cps n k = 
	Printf.printf "fac_cps %i -> \n" n;
	if n = 0 
	then k 1
	else traced_fac_cps (n - 1) 
						(fun v -> Printf.printf "fac_cps %i continues with %i\n" n v;
						 k (n * v));; 	


traced_fac_cps (5) (fun a -> a);;

let rec fib_cps n k = 
	match n with 
	| 0 -> 
		k 0 
	| 1 -> 
		k 1 
	| _ -> fib_cps (n - 1) (fun v1 -> 
				    		fib_cps (n-2) (fun v2 -> 
				    						k (v1 + v2)));;

type int_binary_tree = 
	| Leaf of int 
	| Node of int_binary_tree * int_binary_tree;;


let mult_v0 t_init = 
	let rec visit t = 
		match t with 
		| Leaf n -> 
			if n = 0 then raise n_zero 
			else n 
		| Node (t1, t2) -> 
			(visit t1) * (visit t2)
		in try visit t_init with 
		| is_zero -> 
			0
		| x -> raise x;; 


let mult_v2 t_init k_init = 
	let rec visit t k = 
		match t with 	
		| Leaf n -> 
			k n
		| Node (t1, t2) ->  
			visit t1 (fun n1 -> 
								visit t2 (fun n2 -> 
													k (n1 * n2)))
		in visit t_init k_init;;


let mult_v3 t_init k_init = 
	let rec visit t k = 
		match t with 	
		| Leaf n -> 
			if n = 0 then k_init 0
			else k n
		| Node (t1, t2) ->  
			visit t1 (fun n1 -> 
								visit t2 (fun n2 -> 
													k (n1 * n2)))
		in visit t_init k_init;;








