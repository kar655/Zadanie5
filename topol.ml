open PMap

(** wyjatek rzucany przez [topol] gdy zaleznosci sa cykliczne *)
exception Cykliczne

(* poprawia wejsciowa liste laczac grupy sasiadow *)
let correct lista =
  let out = ref empty in
  let rec helper lis =
    match lis with
    | [] -> !out
    | (x, neigh)::t ->
      (try out := add x (neigh @ (find x !out)) !out with
      Not_found -> out := add x neigh !out);
      helper t
  in helper lista

(* val topol : ('a * 'a list) list -> 'a list *)
(** Dla danej listy [(a_1,[a_11;...;a_1n]); ...; (a_m,[a_m1;...;a_mk])]
    zwraca liste, na ktorej kazdy z elementow a_i oraz a_ij wystepuje
    dokladnie raz i ktora jest uporzadkowana w taki sposob, ze kazdy
    element a_i jest przed kazdym z elementow a_i1 ... a_il *)
let topol (lista: ('a * 'a list) list) =
  let visited = ref empty in    (* wierzcholki odwiedzone *)
  let added = ref empty in      (* wierzcholki dodane *)
  let out = ref [] in           (* wyjscie *)
  let mapa = correct lista in   (* poprawia wejscowa liste na mape *)

  (* jak nie ma sasiadow zwraca wierzcholek *)
  let rec dfs n (l: 'a list) =
    visited := add n n !visited;

    List.iter (fun x ->   (* odpala dfsa po nieodwiedzonych sasiadach *)
      if mem x !visited && not (mem x !added) then
        raise Cykliczne   (* bylem ale nie dodalem *)
      else if not (mem x !added) then
        try dfs x (find x mapa) with
        Not_found ->      (* gdy nie ma sasiadow to dodaje *)
          visited := add x x !visited;
          added := add x x !added;
          out := x :: !out) l;
    (* po sasiadach dodaje do wyniku *)
    added := add n n !added;
    out := n :: !out
  in

  (* glowna petla po wszystkich nieodwiedzonych wierzcholkach
     dla kazdego z nich odpala dfs-a *)
  iter (fun k x ->
    if not (mem k !visited) then
      dfs k x) mapa;
  !out

(* Testy - ze wspólnej puli  *)
(*
exception WA;;
let debug = true;;
(* True if the given order is a correct topological order, *)
(* false otherwise. Checks all edges.                      *)
let test graph order =
  let hashtbl = Hashtbl.create (List.length order)
  in
  List.iteri (fun i x -> Hashtbl.add hashtbl x i) order;
  let check_one (v, l) =
    List.iter (fun u ->
      if (Hashtbl.find hashtbl v) > (Hashtbl.find hashtbl u)
      then raise WA;) l
  in
  try (List.iter check_one graph; true)
  with WA -> false
(* Tests if Topol raises Cykliczne for the given graph *)
let test_cyclic g =
  try let _ = topol g in false
  with Cykliczne -> true
;;

if debug then print_endline "Acyclic correctness tests...";;

let g = [
  ("1", ["2"; "3"]);
  ("3", ["2"]);
  ("4", ["3"; "2"])
];;
assert(test g (topol g));;
let g = [
  ("first", ["second"; "fourth"; "eighth"]);
  ("second", ["fourth"; "eighth"]);
  ("third", ["fourth"; "fifth"; "sixth"]);
  ("fourth", ["eighth"]);
  ("fifth", ["sixth"; "seventh"]);
  ("sixth", ["eighth"; "first"]);
  ("seventh", ["eighth"]);
];;
assert(test g (topol g));;
let g = [
  (1, [2; 3]);
  (2, [4]);
  (3, [4]);
  (4, [5; 6]);
  (5, [7]);
  (6, [7]);
];;
assert(test g (topol g));;
let g = [
  (1, [7; 2]);
  (3, [4; 2; 1; 7; 5]);
  (4, [2; 7; 1]);
  (5, [7; 4; 1; 2]);
  (6, [1; 3; 2; 5; 4; 7]);
  (7, [2])
];;
assert(test g (topol g));;
let g = [
  (1, [2; 4; 8]);
  (2, [16; 32]);
  (4, [64; 128]);
  (8, [256; 512]);
  (16, [1024]);
  (32, [2048]);
  (64, [4096]);
  (128, [8192]);
  (256, [16384]);
  (512, [32768]);
];;
assert(test g (topol g));;
let g = [
  ("Lorem", ["sit"]);
  ("ipsum", ["sit"; "amet"]);
  ("dolor", ["amet"; "elit"]);
  ("sit", ["consectetur"; "adipiscing"; "elit"]);
];;
assert(test g (topol g));;
let g = [];;
assert(test g (topol g));;
let g = [
  ("through", ["the"; "gates"; "of"; "hell"]);
  ("hell", ["as"; "we"; "make"; "our"; "way"; "to"; "heaven"]);
  ("PRIMO", ["VICTORIA"]);
];;
assert(test g (topol g));;
let g = [
  ("one", ["three"]);
  ("one", ["two"]);
  ("two", []);
  ("two", []);
  ("two", ["three"]);
];;
assert(test g (topol g));;
if debug then print_endline "OK";;
if debug then print_endline "Cyclic correctness tests...";;
let g = [
  (10.001, [10.002]);
  (10.002, [10.001])
];;
assert(test_cyclic g);;
let g = [
  (1, [7; 2; 3]);
  (3, [4; 2; 1; 7; 5]);
  (4, [2; 7; 1]);
  (5, [7; 4; 1; 2]);
  (6, [1; 3; 2; 5; 4; 7]);
  (7, [2])
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (2, [3]);
  (3, [4; 5; 3]);
];;
assert(test_cyclic g);;
let g = [
  ("pole", ["pole"; "lyse"; "pole"])
];;
assert(test_cyclic g);;
let g = [
  ("tu", ["tudu"]);
  ("tudu", ["tudu"; "tudu"; "tudu"])
];;
assert(test_cyclic g);;
if debug then print_endline "OK";;
if debug then print_endline "Marcin Michorzewski's acyclic correctness tests...";;
let g = [
  (11, [12]);
  (12, [13]);
  (7, [8]);
  (8, [9]);
  (1, [2]);
  (13, [6]);
  (3, [4]);
  (5, [6]);
  (6, [7]);
  (10, [11])
];;
assert(test g (topol g));;
let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3])
];;
assert(test g (topol g));;
let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14])
];;
assert(test g (topol g));;
let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8])
];;
assert(test g (topol g));;
let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8]);
  (8, [14])
];;
assert(test g (topol g));;
let g = [
  (1, [2]);
  (2, []);
  (3, [2])
];;
assert(test g (topol g));;
let g = [
  ('a', ['e']);
  ('b', ['a'; 'c']);
  ('c', ['a']);
  ('e', [])
];;
assert(test g (topol g));;
if debug then print_endline "OK";;
if debug then print_endline "Marcin Michorzewski's cyclic correctness tests...";;
let g = [
  (3, [4]);
  (5, [6]);
  (6, [7]);
  (10, [11]);
  (11, [12]);
  (12, [13]);
  (7, [8]);
  (9, [13]);
  (8, [9]);
  (1, [2]);
  (13, [6])
];;
assert(test_cyclic g);;
let g = [
  ("Polska", ["Niemcy"]);
  ("Niemcy", ["Polska"])
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (2, [5])
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (1, [5]);
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (2, [6])
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (1, [6])
];;
assert(test_cyclic g);;
let g = [
  (1, [2]);
  (2, [3]);
  (3, [1])
];;
assert(test_cyclic g);;
let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8]);
  (8, [12])
];;
assert(test_cyclic g);;
if debug then print_endline "OK";;
*)
