type key =
|K1 of string
|K2 of string

module Kmod = 
struct
	type t = key
	let compare t1 t2 = 
		match t1,t2 with
		|K1 x, K1 y -> String.compare x y
		|K1 x, K2 y -> 1
		|K2 x, K1 y -> 1
		|K2 x, K2 y -> String.compare x y
		
end
	
module M = Map.Make(Kmod)

let mapadd a b store =
	M.add a b store

let main = 

	let store = M.empty in
	(*let store = mapadd (K1 "4") "5" store in *)
	let store = M.add (K1 "4") "5" store in 
	
	let item = M.find (K1 "4") store in 
	(match item with 
	|"5" -> print_string "found1\n"
	|_ -> print_string "not found\n" );
	
	let store = M.add (K2 "3") "4" store in 

	let item = M.find (K2 "3") store in 
	(match item with 
	|"4" -> print_string "found1\n"
	|_ -> print_string "not found\n" );
	
	let item = M.find (K1 "4") store in 
	(match item with 
	|"5" -> print_string "found1\n"
	|_ -> print_string "not found\n" );
	
	
	
	
