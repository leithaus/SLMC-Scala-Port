(*** Module that handles the abstract syntactic tree representation for processes ***)

exception Ill_formed_ast

(*** Action type ***)
type test =
		Equals | Differs

(*** Action type ***)
type action =
		Input of string * string list
	| Output of string * string list
	| Tau

(*** Abstract syntactic tree for processes type ***)
type piastnode =
		Void
	| Par of piastnode ref * piastnode ref
	| Sum of piastnode ref * piastnode ref
	| New of string list * piastnode ref
	| Act of action * piastnode ref
	| Test of string * string * piastnode ref * test
	| Var of string * string list

(*** Declaration environment type ***)
type dec = Pidec of string list * string list list * (piastnode ref) list

(*** Process environment type ***)
type ast_env = (string, string list * piastnode ref) Hashtbl.t ref

(***)

(*** Computes the set of free names of a process ast ***)

let rec astFN ast ht =
	match !ast with
		Void ->
			ignore ast
	| Par(ast1, ast2) ->
			astFN ast1 ht;
			astFN ast2 ht
	| Sum(ast1, ast2) ->
			astFN ast1 ht;
			astFN ast2 ht
	| New(l, astc) ->
			List.iter (fun id -> Hashtbl.add (!ht) id 0) l;
			astFN astc ht;
			List.iter (fun id -> Hashtbl.remove (!ht) id) l
	| Act(a, astc) ->
			(match a with
					Output(n, ln) ->
						List.iter
							(fun id ->
										if not (Hashtbl.mem (!ht) id) then
											Hashtbl.add (!ht) id 0) (n:: ln);
						astFN astc ht
				| Input(n, ln) ->
						if not (Hashtbl.mem (!ht) n) then
							Hashtbl.add (!ht) n 0;
						List.iter (fun id -> Hashtbl.add (!ht) id 0) ln;
						astFN astc ht;
						List.iter (fun id -> Hashtbl.remove (!ht) id) ln
				| Tau -> astFN astc ht)
	| Test(id1, id2, astc, typ) ->
			if not (Hashtbl.mem (!ht) id1) then
				Hashtbl.add (!ht) id1 0;
			if not (Hashtbl.mem (!ht) id2) then
				Hashtbl.add (!ht) id2 0;
			astFN astc ht
	| Var(s, aL) ->
			List.iter
				(fun id ->
							if not (Hashtbl.mem (!ht) id) then
								Hashtbl.add (!ht) id 0) aL

(***)

(* Auxiliar function to print_ast *)

let rec print_idlist lst flag =
	match lst with
		[] ->
			if flag then
				print_string " "
	| h::[] ->
			print_string h;
			if flag then
				print_string " "
	| h:: t ->
			print_string h;
			print_string ",";
			print_idlist t flag

(*** Prints a process ast to stdout ***)

let rec print_ast ast =
	match !ast with
		Void ->
			print_string "0"
	| Par(ast1, ast2) ->
			print_string "(";
			print_ast ast1;
			print_string " | ";
			print_ast ast2;
			print_string ")"
	| Sum(ast1, ast2) ->
			print_string "{";
			print_ast ast1;
			print_string " + ";
			print_ast ast2;
			print_string "}"
	| New(lst, ast1) ->
			print_string "new ";
			print_idlist lst true;
			print_string "in ";
			print_ast ast1
	| Act(a, ast1) ->
			(match a with
					Input(n1, n2) ->
						print_string n1;
						print_string "?(";
						print_idlist n2 false;
						print_string ").";
						print_ast ast1
				| Output(n1, n2) ->
						print_string n1;
						print_string "!(";
						print_idlist n2 false;
						print_string ").";
						print_ast ast1
				| Tau ->
						print_string "tau.";
						print_ast ast1)
	| Test(id1, id2, ast1, typ) ->
			print_string "[";
			print_string id1;
			(if (typ = Equals) then
					print_string "="
				else
					print_string "!=");
			print_string id2;
			print_string "].";
			print_ast ast1
	| Var(x, aL) ->
			print_string x;
			if List.length aL > 0 then
				(print_string "(";
					print_idlist aL false;
					print_string ")")

(***)
