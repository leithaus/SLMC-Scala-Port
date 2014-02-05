(*** Module that handles the abstract syntactic tree representation for formulas ***)

exception Ill_formed_form

(*** Label type ***)

type lab = 
    OutLab of string * string list
  | InpLab of string * string list

(*** Number of components formula variants ***)

type numCompsType = EqNum | GtNum | LtNum

(*** Abstract syntactic tree for formulas type ***)

type formastnode = 
    True
  | False
  | Void
  | NumComps of int * numCompsType
  | Eq of string * string
  | Neq of string * string
  | Comp of formastnode * formastnode 
  | Decomp of formastnode * formastnode
  | Not of formastnode
  | And of formastnode * formastnode
  | Or of formastnode * formastnode
  | Implies of formastnode * formastnode
  | Equiv of formastnode * formastnode
  | Reveal of string * formastnode
  | RevealAll of string * formastnode
  | Fresh of string * formastnode
  | Free of string
  | Hidden of string * formastnode
  | MayTau of formastnode
  | AllTau of formastnode
  | MayLab of lab * formastnode
  | AllLab of lab * formastnode
  | MayOutN of string * formastnode
  | MayInpN of string * formastnode
  | AllOutN of string * formastnode
  | AllInpN of string * formastnode
  | MayOut of formastnode
  | MayInp of formastnode
  | AllOut of formastnode
  | AllInp of formastnode
  | MayN of string * formastnode
  | AllN of string * formastnode
  | May of formastnode
  | All of formastnode
  | Exists of string * formastnode
  | ForAll of string * formastnode
  | MaxFix of string * string list * formastnode * string list
  | MinFix of string * string list * formastnode * string list
  | Eventually of formastnode
  | Always of formastnode
  | Inside of formastnode
  | Show_f of formastnode
  | Show_s of formastnode
  | PropVar of string * string list
  | Abbrev of string * formastnode list

(*** Declaration type ***)

type declaration = Dec of ((string * string list * string list) * formastnode)

(***)

(* Auxiliar functions to print_form *)

let rec print_ids l =
  match l with
    [] -> print_string ""
  | hd::[] -> print_string hd
  | hd::tl -> print_string (hd^","); print_ids tl

let print_label l =
  match l with
    OutLab(s, sl) -> print_string s; print_string "!("; print_ids sl; print_string ")"
  | InpLab(s, sl) -> print_string s; print_string "?("; print_ids sl; print_string ")"

(*** Prints a formula ast to stdout ***)

let rec print_form f =
  match f with
    True -> print_string "true"
  | False -> print_string "false"
  | Void -> print_string "void"
  | NumComps(i,t) -> 
      (match t with
	EqNum -> print_int i
      | LtNum -> print_string "<"; print_int i
      | GtNum -> print_string ">"; print_int i)
  | Eq(id1,id2) -> print_string (id1^"=="^id2)
  | Neq(id1,id2) -> print_string (id1^"!="^id2)
  | Comp(f1,f2) -> 
      print_string "(";
      print_form f1;
      print_string " | ";
      print_form f2;
      print_string ")"
  | Decomp(f1,f2) ->
      print_string "(";
      print_form f1;
      print_string " || ";
      print_form f2;
      print_string ")"
  | Not(f1) ->
      print_string "not (";
      print_form f1;
      print_string ")"
  | And(f1,f2) ->
      print_string "(";
      print_form f1;
      print_string " and ";
      print_form f2;
      print_string ")"
  | Or(f1,f2) ->
      print_string "(";
      print_form f1;
      print_string " or ";
      print_form f2;
      print_string ")"
  | Implies(f1,f2) ->
      print_string "(";
      print_form f1;
      print_string " => ";
      print_form f2;
      print_string ")"
  | Equiv(f1,f2) ->
      print_string "(";
      print_form f1;
      print_string " <=> ";
      print_form f2;
      print_string ")"
  | Reveal(s,f1) ->
      print_string ("reveal "^s^".(");
      print_form f1;
      print_string ")"
  | RevealAll(s,f1) ->
      print_string ("revealall "^s^".(");
      print_form f1;
      print_string ")"
  | Fresh(s,f1) ->
      print_string ("fresh "^s^".(");
      print_form f1;
      print_string ")"
  | Free(s) ->
      print_string ("@"^s);
  | Hidden(s,f1) ->
      print_string ("hidden "^s^".(");
      print_form f1;
      print_string ")"
  | MayTau(f1) ->
      print_string "<> (";
      print_form f1;
      print_string ")"
  | AllTau(f1) ->
      print_string "[] (";
      print_form f1;
      print_string ")"
  | MayLab(l,f1) ->
      print_string "<";
      print_label l;
      print_string "> (";
      print_form f1;
      print_string ")"
  | AllLab(l,f1) ->
      print_string "[";
      print_label l;
      print_string "] (";
      print_form f1;
      print_string ")"
  | MayOutN(n,f1) ->
      print_string ("<"^n^"!> (");
      print_form f1;
      print_string ")"
  | MayInpN(n,f1) ->
      print_string ("<"^n^"?> (");
      print_form f1;
      print_string ")"
  | AllOutN(n,f1) ->
      print_string ("["^n^"!] (");
      print_form f1;
      print_string ")"
  | AllInpN(n,f1) ->
      print_string ("["^n^"?] (");
      print_form f1;
      print_string ")"
  | MayOut(f1) ->
      print_string ("<!> (");
      print_form f1;
      print_string ")"
  | MayInp(f1) ->
      print_string ("<?> (");
      print_form f1;
      print_string ")"
  | AllOut(f1) ->
      print_string ("[!] (");
      print_form f1;
      print_string ")"
  | AllInp(f1) ->
      print_string ("[?] (");
      print_form f1;
      print_string ")"
  | MayN(n,f1) ->
      print_string ("<"^n^"> (");
      print_form f1;
      print_string ")"
  | AllN(n,f1) ->
      print_string ("["^n^"] (");
      print_form f1;
      print_string ")"
  | May(f1) ->
      print_string ("<*> (");
      print_form f1;
      print_string ")"
  | All(f1) ->
      print_string ("[*] (");
      print_form f1;
      print_string ")"
  | Exists(s,f1) ->
      print_string ("exists "^s^".(");
      print_form f1;
      print_string ")"
  | ForAll(s,f1) ->
      print_string ("forall "^s^".(");
      print_form f1;
      print_string ")"
  | MaxFix(x,paramsList,f1,argsList) ->
      print_string ("(maxfix "^x);
      (if not (List.length paramsList == 0) then
        (print_string "(";
        print_ids paramsList;
	print_string ")"));
      print_string ".(";
      print_form f1;
      print_string "))";
      (if List.length argsList > 0 then
        (print_string "(";
        print_ids argsList;
        print_string ")"))
  | MinFix(x,paramsList,f1,argsList) ->
      print_string ("(minfix "^x);
      (if not (List.length paramsList == 0) then
        (print_string "(";
        print_ids paramsList;
	print_string ")"));
      print_string ".(";
      print_form f1;
      print_string "))";
      (if List.length argsList > 0 then
        (print_string "(";
        print_ids argsList;
        print_string ")"))
  | Eventually(f1) ->
      print_string ("eventually (");
      print_form f1;
      print_string ")"
  | Always(f1) ->
      print_string ("always (");
      print_form f1;
      print_string ")"
  | Inside(f1) ->
      print_string ("inside (");
      print_form f1;
      print_string ")"
  | Show_f(f1) ->
      print_string ("show_fail (");
      print_form f1;
      print_string ")"
  | Show_s(f1) ->
      print_string ("show_succeed (");
      print_form f1;
      print_string ")"
  | PropVar(p,paramsList) ->
      print_string p;
      (if List.length paramsList > 0 then
        (print_string "(";
        print_ids paramsList;
	print_string ")"))
  | Abbrev(id, fs) ->
      print_string id;
      (if List.length fs > 0 then
	(print_string "(";
	 print_forms fs;
	 print_string ")"))

and print_forms l =
  match l with
    [] -> print_string ""
  | hd::[] -> print_form hd
  | hd::tl -> print_form hd; print_string ","; print_forms tl

(***)

(* Auxiliar functions to print_form_subst *)

let rec print_ids_subst l nenv =
  match l with
    [] -> print_string ""
  | hd::[] -> 
      let nhd = try Hashtbl.find !nenv hd with Not_found -> hd in
      print_string nhd
  | hd::tl -> 
      let nhd = try Hashtbl.find !nenv hd with Not_found -> hd in
      print_string (nhd^","); print_ids_subst tl nenv

let print_label_subst l nenv =
  match l with
    OutLab(s, sl) -> 
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      print_string ns; 
      print_string "!("; 
      print_ids_subst sl nenv; 
      print_string ")"
  | InpLab(s, sl) -> 
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      print_string ns; 
      print_string "?("; 
      print_ids_subst sl nenv; 
      print_string ")"

(*** Prints a formula ast to stdout regarding a name substitution environment ***)

let rec print_form_subst f nenv =
  match f with
    True -> print_string "true"
  | False -> print_string "false"
  | Void -> print_string "void"
  | NumComps(i,t) -> 
      (match t with
	EqNum -> print_int i
      | LtNum -> print_string "<"; print_int i
      | GtNum -> print_string ">"; print_int i)
  | Eq(id1,id2) -> 
      let nid1 = try Hashtbl.find !nenv id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !nenv id2 with Not_found -> id2 in
      print_string (nid1^"=="^nid2)
  | Neq(id1,id2) -> 
      let nid1 = try Hashtbl.find !nenv id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !nenv id2 with Not_found -> id2 in
      print_string (nid1^"!="^nid2)
  | Comp(f1,f2) -> 
      print_string "(";
      print_form_subst f1 nenv;
      print_string " | ";
      print_form_subst f2 nenv;
      print_string ")"
  | Decomp(f1,f2) ->
      print_string "(";
      print_form_subst f1 nenv;
      print_string " || ";
      print_form_subst f2 nenv;
      print_string ")"
  | Not(f1) ->
      print_string "not (";
      print_form_subst f1 nenv;
      print_string ")"
  | And(f1,f2) ->
      print_string "(";
      print_form_subst f1 nenv;
      print_string " and ";
      print_form_subst f2 nenv;
      print_string ")"
  | Or(f1,f2) ->
      print_string "(";
      print_form_subst f1 nenv;
      print_string " or ";
      print_form_subst f2 nenv;
      print_string ")"
  | Implies(f1,f2) ->
      print_string "(";
      print_form_subst f1 nenv;
      print_string " => ";
      print_form_subst f2 nenv;
      print_string ")"
  | Equiv(f1,f2) ->
      print_string "(";
      print_form_subst f1 nenv;
      print_string " <=> ";
      print_form_subst f2 nenv;
      print_string ")"
  | Reveal(s,f1) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      print_string ("reveal "^ns^".(");
      print_form_subst f1 nenv;
      print_string ")"
  | RevealAll(s,f1) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      print_string ("revealall "^ns^".(");
      print_form_subst f1 nenv;
      print_string ")"
  | Fresh(s,f1) ->
      Hashtbl.add !nenv s s;
      print_string ("fresh "^s^".(");
      print_form_subst f1 nenv;
      print_string ")";
      Hashtbl.remove !nenv s
  | Free(s) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      print_string ("@"^ns);
  | Hidden(s,f1) ->
      Hashtbl.add !nenv s s;
      print_string ("hidden "^s^".(");
      print_form_subst f1 nenv;
      print_string ")";
      Hashtbl.remove !nenv s
  | MayTau(f1) ->
      print_string "<> (";
      print_form_subst f1 nenv;
      print_string ")"
  | AllTau(f1) ->
      print_string "[] (";
      print_form_subst f1 nenv;
      print_string ")"
  | MayLab(l,f1) ->
      print_string "<";
      print_label_subst l nenv;
      print_string "> (";
      print_form_subst f1 nenv;
      print_string ")"
  | AllLab(l,f1) ->
      print_string "[";
      print_label_subst l nenv;
      print_string "] (";
      print_form_subst f1 nenv;
      print_string ")"
  | MayOutN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("<"^nn^"!> (");
      print_form_subst f1 nenv;
      print_string ")"
  | MayInpN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("<"^nn^"?> (");
      print_form_subst f1 nenv;
      print_string ")"
  | AllOutN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("["^nn^"!] (");
      print_form_subst f1 nenv;
      print_string ")"
  | AllInpN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("["^nn^"?] (");
      print_form_subst f1 nenv;
      print_string ")"
  | MayOut(f1) ->
      print_string ("<!> (");
      print_form_subst f1 nenv;
      print_string ")"
  | MayInp(f1) ->
      print_string ("<?> (");
      print_form_subst f1 nenv;
      print_string ")"
  | AllOut(f1) ->
      print_string ("[!] (");
      print_form_subst f1 nenv;
      print_string ")"
  | AllInp(f1) ->
      print_string ("[?] (");
      print_form_subst f1 nenv;
      print_string ")"
  | MayN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("<"^nn^"> (");
      print_form_subst f1 nenv;
      print_string ")"
  | AllN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      print_string ("["^nn^"] (");
      print_form_subst f1 nenv;
      print_string ")"
  | May(f1) ->
      print_string ("<*> (");
      print_form_subst f1 nenv;
      print_string ")"
  | All(f1) ->
      print_string ("[*] (");
      print_form_subst f1 nenv;
      print_string ")"
  | Exists(s,f1) ->
      Hashtbl.add !nenv s s;
      print_string ("exists "^s^".(");
      print_form_subst f1 nenv;
      print_string ")";
      Hashtbl.remove !nenv s
  | ForAll(s,f1) ->
      Hashtbl.add !nenv s s;
      print_string ("forall "^s^".(");
      print_form_subst f1 nenv;
      print_string ")";
      Hashtbl.remove !nenv s
  | MaxFix(x,paramsList,f1,argsList) ->
      print_string ("(maxfix "^x);
      (if not (List.length paramsList == 0) then
        (print_string "(";
         List.iter (fun id -> Hashtbl.add !nenv id id) paramsList;
	 print_ids_subst paramsList nenv;
	 print_string ")"));
      print_string ".(";
      print_form_subst f1 nenv;
      print_string "))";
      (if List.length argsList > 0 then
        (print_string "(";
         print_ids_subst argsList nenv;
	 List.iter (fun id -> Hashtbl.remove !nenv id) paramsList;
         print_string ")"))
  | MinFix(x,paramsList,f1,argsList) ->
      print_string ("(minfix "^x);
      (if not (List.length paramsList == 0) then
        (print_string "(";
         List.iter (fun id -> Hashtbl.add !nenv id id) paramsList;
         print_ids_subst paramsList nenv;
	 print_string ")"));
      print_string ".(";
      print_form_subst f1 nenv;
      print_string "))";
      (if List.length argsList > 0 then
        (print_string "(";
         print_ids_subst argsList nenv;
         List.iter (fun id -> Hashtbl.remove !nenv id) paramsList;
         print_string ")"))
  | Eventually(f1) ->
      print_string ("eventually (");
      print_form_subst f1 nenv;
      print_string ")"
  | Always(f1) ->
      print_string ("always (");
      print_form_subst f1 nenv;
      print_string ")"
  | Inside(f1) ->
      print_string ("inside (");
      print_form_subst f1 nenv;
      print_string ")"
  | Show_f(f1) ->
      print_string ("show_fail (");
      print_form_subst f1 nenv;
      print_string ")"
  | Show_s(f1) ->
      print_string ("show_succeed (");
      print_form_subst f1 nenv;
      print_string ")"
  | PropVar(p,paramsList) ->
      print_string p;
      (if List.length paramsList > 0 then
        print_string "(";
        print_ids_subst paramsList nenv;
	print_string ")") 
  | Abbrev(id, fs) ->
      print_string (id^"(");
      print_forms_subst fs nenv;
      print_string ")"

and print_forms_subst l nenv =
  match l with
    [] -> print_string ""
  | hd::[] -> print_form_subst hd nenv
  | hd::tl -> print_form_subst hd nenv; print_string ","; print_forms_subst tl nenv

(***)

(* Auxiliar functions to formFN *)

let labelFN l h res nenv = 
  let (s,sl) = 
    (match l with
      InpLab(i,il) -> (i,il)
    | OutLab(o,ol) -> (o,ol)) in
  List.iter 
    (fun id -> 
      if id <> "_" then
         (let nid = try Hashtbl.find !nenv id with Not_found -> id in
         if not (Hashtbl.mem !h nid) then Hashtbl.add !h nid true; res := nid::!res)) (s::sl)

let rec formFN_aux f h res env pvars nenv =
  match f with
    True -> ignore f 
  | False -> ignore f 
  | Void -> ignore f
  | NumComps(i,t) -> ignore f
  | Eq(id1,id2) -> 
      let nid1 = try Hashtbl.find !nenv id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !nenv id2 with Not_found -> id2 in
      if not (Hashtbl.mem !h nid1) then
	(Hashtbl.add !h nid1 true;
	 res := nid1::!res);
      if not (Hashtbl.mem !h nid2) then
	(Hashtbl.add !h nid2 true;
	 res := nid2::!res)
  | Neq(id1,id2) ->
      let nid1 = try Hashtbl.find !nenv id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !nenv id2 with Not_found -> id2 in
      if not (Hashtbl.mem !h nid1) then
	(Hashtbl.add !h nid1 true;
	 res := nid1::!res);
      if not (Hashtbl.mem !h nid2) then
	(Hashtbl.add !h nid2 true;
	 res := nid2::!res)
  | Comp(f1,f2) -> 
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Decomp(f1,f2) ->
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Not(f1) ->
      formFN_aux f1 h res env pvars nenv
  | And(f1,f2) ->
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Or(f1,f2) ->
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Implies(f1,f2) ->
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Equiv(f1,f2) ->
      formFN_aux f1 h res env pvars nenv;
      formFN_aux f2 h res env pvars nenv
  | Reveal(s,f1) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      if not (Hashtbl.mem !h ns) then
	(Hashtbl.add !h ns true;
	 res := ns::!res);
      formFN_aux f1 h res env pvars nenv
  | RevealAll(s,f1) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      if not (Hashtbl.mem !h ns) then
	(Hashtbl.add !h ns true;
	 res := ns::!res);
      formFN_aux f1 h res env pvars nenv
  | Fresh(s,f1) ->
      Hashtbl.add !nenv s s;
      Hashtbl.add !h s false;
      formFN_aux f1 h res env pvars nenv;
      Hashtbl.remove !nenv s;
      Hashtbl.remove !h s
  | Free(s) ->
      let ns = try Hashtbl.find !nenv s with Not_found -> s in
      if not (Hashtbl.mem !h ns) then
	(Hashtbl.add !h ns true;
	 res := ns::!res)
  | Hidden(s,f1) ->
      Hashtbl.add !nenv s s;
      Hashtbl.add !h s false;
      formFN_aux f1 h res env pvars nenv;
      Hashtbl.remove !nenv s;
      Hashtbl.remove !h s
  | MayTau(f1) ->
      formFN_aux f1 h res env pvars nenv
  | AllTau(f1) ->
      formFN_aux f1 h res env pvars nenv
  | MayLab(l,f1) ->
      labelFN l h res nenv;
      formFN_aux f1 h res env pvars nenv
  | AllLab(l,f1) ->
      labelFN l h res nenv;
      formFN_aux f1 h res env pvars nenv
  | MayOutN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | MayInpN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | AllOutN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | AllInpN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | MayOut(f1) ->
      formFN_aux f1 h res env pvars nenv
  | MayInp(f1) ->
      formFN_aux f1 h res env pvars nenv
  | AllOut(f1) ->
      formFN_aux f1 h res env pvars nenv
  | AllInp(f1) ->
      formFN_aux f1 h res env pvars nenv
  | MayN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | AllN(n,f1) ->
      let nn = try Hashtbl.find !nenv n with Not_found -> n in
      if not (Hashtbl.mem !h nn) then
	(Hashtbl.add !h nn true;
	 res := nn::!res);
      formFN_aux f1 h res env pvars nenv
  | May(f1) ->
      formFN_aux f1 h res env pvars nenv
  | All(f1) ->
      formFN_aux f1 h res env pvars nenv
  | Exists(s,f1) ->
      Hashtbl.add !nenv s s;
      Hashtbl.add !h s false;
      formFN_aux f1 h res env pvars nenv;
      Hashtbl.remove !nenv s;
      Hashtbl.remove !h s
  | ForAll(s,f1) ->
      Hashtbl.add !nenv s s;
      Hashtbl.add !h s false;
      formFN_aux f1 h res env pvars nenv;
      Hashtbl.remove !nenv s;
      Hashtbl.remove !h s
  | MaxFix(x,paramsList,f1,argsList) -> 
      Hashtbl.add !env x false;
      List.iter (fun n -> Hashtbl.add !nenv n n) paramsList;
      List.iter (fun n -> Hashtbl.add !h n false) paramsList;
      formFN_aux f1 h res env pvars nenv;
      List.iter (fun n -> Hashtbl.remove !nenv n ) paramsList;
      List.iter (fun n -> Hashtbl.remove !h n ) paramsList;
      List.iter (fun n ->
			let nn = try Hashtbl.find !nenv n with Not_found -> n in
			if not (Hashtbl.mem !h nn) then
			(Hashtbl.add !h nn true;
			res := nn::!res)) argsList;
      Hashtbl.remove !env x
  | MinFix(x,paramsList,f1,argsList) -> 
      Hashtbl.add !env x false;
      List.iter (fun n -> Hashtbl.add !nenv n n) paramsList;
      List.iter (fun n -> Hashtbl.add !h n false) paramsList;
      formFN_aux f1 h res env pvars nenv;
      List.iter (fun n -> Hashtbl.remove !nenv n ) paramsList;
      List.iter (fun n -> Hashtbl.remove !h n ) paramsList;
      List.iter (fun n ->
			let nn = try Hashtbl.find !nenv n with Not_found -> n in
			if not (Hashtbl.mem !h nn) then
			(Hashtbl.add !h nn true;
			res := nn::!res)) argsList;
      Hashtbl.remove !env x
  | Eventually(f1) ->
      formFN_aux f1 h res env pvars nenv
  | Always(f1) ->
      formFN_aux f1 h res env pvars nenv
  | Inside(f1) ->
      formFN_aux f1 h res env pvars nenv
  | Show_f(f1) ->
      formFN_aux f1 h res env pvars nenv
  | Show_s(f1) ->
      formFN_aux f1 h res env pvars nenv
  | PropVar(p,paramsList) ->
      if not (Hashtbl.mem !env p) then
	(Hashtbl.add !env p true;
	 pvars := p::!pvars);
      List.iter (fun n ->
			let nn = try Hashtbl.find !nenv n with Not_found -> n in
			if not (Hashtbl.mem !h nn) then
			(Hashtbl.add !h nn true;
			res := nn::!res)) paramsList;
  | Abbrev(id, fs) ->
      ignore f

(*** Computes the set of free names and free propositional variables of a formula ast ***)

let formFN f nenv =
  let h1 = ref (Hashtbl.create 100) in
  let res = ref [] in
  let h2 = ref (Hashtbl.create 100) in
  let pvars = ref [] in
  formFN_aux f h1 res h2 pvars nenv;
  (!res,!pvars)

(***)

(* Auxiliar functions to subst *)

let subst_name n h aux res =
  if n = "_" then n
  else
  (let nn = try Hashtbl.find !h n with Not_found -> n in
  if not (Hashtbl.mem !aux nn) then
    (Hashtbl.add !aux nn true;
     res := nn::!res);
  nn)

let rec subst_nameL nL h aux res =
  match nL with
    [] -> []
  | hd::tl -> (subst_name hd h aux res)::(subst_nameL tl h aux res)

let subst_label l h aux res =
  match l with
    InpLab(i,il) -> InpLab(subst_name i h aux res, subst_nameL il h aux res)
  | OutLab(o,ol) -> OutLab(subst_name o h aux res, subst_nameL ol h aux res)

let rec subst_aux f h aux res pvars pvars_env =
  match f with
    True -> True
  | False -> False
  | Void -> Void
  | NumComps(i,t) -> NumComps(i,t)
  | Eq(id1,id2) -> 
      let nid1 = try Hashtbl.find !h id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !h id2 with Not_found -> id2 in
      if not (Hashtbl.mem !aux nid1) then
	(Hashtbl.add !aux nid1 true;
	 res := nid1::!res);
      if not (Hashtbl.mem !aux nid2) then
	(Hashtbl.add !aux nid2 true;
	 res := nid2::!res);
      Eq(nid1,nid2)
  | Neq(id1,id2) ->
      let nid1 = try Hashtbl.find !h id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find !h id2 with Not_found -> id2 in
      if not (Hashtbl.mem !aux nid1) then
	(Hashtbl.add !aux nid1 true;
	 res := nid1::!res);
      if not (Hashtbl.mem !aux nid2) then
	(Hashtbl.add !aux nid2 true;
	 res := nid2::!res);
      Neq(nid1,nid2)
  | Comp(f1,f2) -> Comp(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Decomp(f1,f2) -> Decomp(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Not(f1) -> Not(subst_aux f1 h aux res pvars pvars_env)
  | And(f1,f2) -> And(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Or(f1,f2) -> Or(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Implies(f1,f2) -> Implies(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Equiv(f1,f2) -> Equiv(subst_aux f1 h aux res pvars pvars_env, subst_aux f2 h aux res pvars pvars_env)
  | Reveal(s,f1) ->
      let ns = try Hashtbl.find !h s with Not_found -> s in
      if not (Hashtbl.mem !aux ns) then
	(Hashtbl.add !aux ns true;
	 res := ns::!res);
      Reveal(ns, subst_aux f1 h aux res pvars pvars_env)
  | RevealAll(s,f1) ->
      let ns = try Hashtbl.find !h s with Not_found -> s in
      if not (Hashtbl.mem !aux ns) then
	(Hashtbl.add !aux ns true;
	 res := ns::!res);
      RevealAll(ns, subst_aux f1 h aux res pvars pvars_env)
  | Fresh(s,f1) ->
      Hashtbl.add !h s s;
      Hashtbl.add !aux s false;
      let res = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !h s;
      Hashtbl.remove !aux s;
      Fresh(s,res)
  | Free(s) ->
      let ns = try Hashtbl.find !h s with Not_found -> s in
      if not (Hashtbl.mem !aux ns) then
	(Hashtbl.add !aux ns true;
	 res := ns::!res);
      Free(ns)
  | Hidden(s,f1) ->
      Hashtbl.add !h s s;
      Hashtbl.add !aux s false;
      let res = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !h s;
      Hashtbl.remove !aux s;
      Hidden(s,res)
  | MayTau(f1) -> MayTau(subst_aux f1 h aux res pvars pvars_env)
  | AllTau(f1) -> AllTau(subst_aux f1 h aux res pvars pvars_env)
  | MayLab(l,f1) ->
      let nl = subst_label l h aux res in
      MayLab(nl,subst_aux f1 h aux res pvars pvars_env)
  | AllLab(l,f1) ->
      let nl = subst_label l h aux res in
      AllLab(nl,subst_aux f1 h aux res pvars pvars_env)
  | MayOutN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      MayOutN(nn,subst_aux f1 h aux res pvars pvars_env)
  | MayInpN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      MayInpN(nn,subst_aux f1 h aux res pvars pvars_env)
  | AllOutN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      AllOutN(nn,subst_aux f1 h aux res pvars pvars_env)
  | AllInpN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      AllInpN(nn,subst_aux f1 h aux res pvars pvars_env)
  | MayOut(f1) -> MayOut(subst_aux f1 h aux res pvars pvars_env)
  | MayInp(f1) -> MayInp(subst_aux f1 h aux res pvars pvars_env)
  | AllOut(f1) -> AllOut(subst_aux f1 h aux res pvars pvars_env)
  | AllInp(f1) -> AllInp(subst_aux f1 h aux res pvars pvars_env)
  | MayN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      MayN(nn, subst_aux f1 h aux res pvars pvars_env)
  | AllN(n,f1) ->
      let nn = try Hashtbl.find !h n with Not_found -> n in
      if not (Hashtbl.mem !aux nn) then
	(Hashtbl.add !aux nn true;
	 res := nn::!res);
      AllN(nn, subst_aux f1 h aux res pvars pvars_env)
  | May(f1) -> May(subst_aux f1 h aux res pvars pvars_env)
  | All(f1) -> All(subst_aux f1 h aux res pvars pvars_env)
  | Exists(s,f1) ->
      Hashtbl.add !h s s;
      Hashtbl.add !aux s false;
      let res = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !h s;
      Hashtbl.remove !aux s;
      Exists(s,res)
  | ForAll(s,f1) ->
      Hashtbl.add !h s s;
      Hashtbl.add !aux s false;
      let res = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !h s;
      Hashtbl.remove !aux s;
      ForAll(s,res)
  | MaxFix(x,params,f1,args) -> 
      Hashtbl.add !pvars_env x false;
      List.iter (fun n -> Hashtbl.add !aux n false) params;
      List.iter (fun n -> Hashtbl.add !h n n) params;
      let result = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !pvars_env x;
      List.iter (fun n -> Hashtbl.remove !aux n) params;
      List.iter (fun n -> Hashtbl.remove !h n) params;
      MaxFix(x, params, result, subst_nameL args h aux res)
  | MinFix(x,params,f1,args) -> 
      Hashtbl.add !pvars_env x false;
      List.iter (fun n -> Hashtbl.add !aux n false) params;
      List.iter (fun n -> Hashtbl.add !h n n) params;
      let result = subst_aux f1 h aux res pvars pvars_env in
      Hashtbl.remove !pvars_env x;
      List.iter (fun n -> Hashtbl.remove !aux n) params;
      List.iter (fun n -> Hashtbl.remove !h n) params;
      MinFix(x, params, result, subst_nameL args h aux res)
  | Eventually(f1) -> Eventually(subst_aux f1 h aux res pvars pvars_env)
  | Always(f1) -> Always(subst_aux f1 h aux res pvars pvars_env)
  | Inside(f1) -> Inside(subst_aux f1 h aux res pvars pvars_env)
  | Show_f(f1) -> Show_f(subst_aux f1 h aux res pvars pvars_env)
  | Show_s(f1) -> Show_s(subst_aux f1 h aux res pvars pvars_env)
  | PropVar(p,args) -> 
      if not (Hashtbl.mem !pvars_env p) then
	(Hashtbl.add !pvars_env p true;
	 pvars := p::!pvars); 
      PropVar(p, subst_nameL args h aux res)
  | Abbrev(id, fs) -> Abbrev(id,fs)

(*** Returns the formula ast, the free names and the free propositional variables regarding a name substitution ***)

let subst f h =
  let aux = ref (Hashtbl.create 100) in
  let res = ref [] in
  let pvars_env = ref (Hashtbl.create 100) in
  let pvars = ref [] in
  let new_form = subst_aux f h aux res pvars pvars_env in
  (new_form,!res,!pvars)

(***)
