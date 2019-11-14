(* fib-with-trace.ml *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* for Jeremy Ern in FPP *)
(* Version of Mon 25 Sep 2017 *)

(* ********** *)

(* Unparsing integers and pairs of integers: *)

let show_int n =
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

let show_pair_of_ints (i, j) =
  "(" ^ show_int i ^ ", " ^ show_int j ^ ")"

(* ********** *)

(* Making an indentation: *)

let make_indentation n =
  String.make (2 * n) ' ';;

(* ********** *)

(* Fibonacci function with two accumulators: *)

let rec fib_v2_aux n a1 a2 =
  if n = 0
  then a1
  else fib_v2_aux (n - 1) a2 (a1 + a2);;

let fib_v2 n =
  fib_v2_aux n 0 1;;

(* ***** *)

(* Traced version: *)

let rec traced_fib_v2_aux n a1 a2 =
let () = Printf.printf "fib_v2_aux %s %s %s ->\n" (show_int n) (show_int a1) (show_int a2) in
  if n = 0
  then a1
  else traced_fib_v2_aux (n - 1) a2 (a1 + a2);;

let traced_fib_v2 n =
  traced_fib_v2_aux n 0 1;;


(* ********** *)

(* Fibonacci function with two co-accumulators: *)

let rec fib_v3_aux n =
  if n = 0
  then (0, 1)
  else let (a1, a2) = fib_v3_aux (n - 1)
       in (a2, a1 + a2);;

let fib_v3 n =
  let (a1, _) = fib_v3_aux n
  in a1;;

(* ***** *)

(* Traced version: *)

let rec traced_fib_v3_aux n depth =
let () = Printf.printf "%sfib_v3_aux (%s) ->\n" (make_indentation depth) (show_int n) in
  let result = (if n = 0
                then (0, 1)
                else let (a1, a2) = traced_fib_v3_aux (n - 1) (depth + 1)
                     in (a2, a1 + a2)) in
  let () = Printf.printf "%sfib_v3_aux (%s) <- %s\n" (make_indentation depth) (show_int n) (show_pair_of_ints result) in 
  result;;


let traced_fib_v3 n =
  let (a1, _) = traced_fib_v3_aux n 0
  in a1;;


traced_fib_v2 6;;
traced_fib_v3 6;;


(* ********** *)

(* fib-with-trace.ml *)

