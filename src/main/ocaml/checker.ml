(*** Module that implements the model checking algorithm ***)

open Namegen
open Piastnode
open Ccastnode
open Equations
open Process
open Iterator
open Formastnode
open Mcmenu

(***)

exception Undeclared of string
exception Wrong_args of string
exception ErrorMsg of string
exception UnguardedRec of string
exception MaxThreads

(***)

(* Fixpoint type *)

type fixpoints = Max | Min

(***)

(* Data structures that handle process representations *)

let astprocs = ref (Hashtbl.create 100)
let printprocs = ref []
let ccprocs = ref []
let cdlspecs = ref []
let procs = ref (Hashtbl.create 100)

(* Data structures that handle formula representations *)

let printforms = ref []
let forms = ref (Hashtbl.create 100)

(* Model checker's user configurable parameters *)

let trace_value = ref false
let max_threads = ref 50
let show_time = ref false
let show_checkcounter = ref false
let show_states = false
let show_counter = ref 0
let check_counter = ref 0

(***)

(* Auxiliar function to print_procs *)

let rec print_names l = 
  match l with
    [] -> print_string ""
  | hd::[] -> print_string hd
  | hd::tl -> print_string (hd^","); print_names tl

let rec print_ands idL paramL pL visited =
  match idL with
    [] -> print_string ";\n"
  | hd::tl -> 
      if (Hashtbl.mem visited hd) then
	print_ands tl (List.tl paramL) (List.tl pL) visited
      else
	(Hashtbl.add visited hd true;
	 print_string ("\nand "^hd);
	 if (List.length (List.hd paramL)) > 0 then
	   (print_string "(";
	    print_names (List.hd paramL);
	    print_string ")");
	 print_string " = ";
	 print_ast (List.hd pL);
	 print_ands tl (List.tl paramL) (List.tl pL) visited)

let rec print_procs_aux l visited =
  match l with
    [] -> ignore l
  | (id,dec)::tl ->
      if Hashtbl.mem visited id then
	print_procs_aux tl visited
      else
	(match dec with Pidec(ids, params, ps) ->
	  List.iter (fun id_proc -> Hashtbl.add visited id_proc true) ids;
	  print_procs_aux tl visited;
	  print_string ("defproc "^id);
	  if List.length (List.hd params) > 0 then
	    (print_string "(";
	     print_names (List.hd params);
	     print_string ")");
	  print_string " = ";
	  print_ast (List.hd ps);
	  List.iter (fun id_proc -> Hashtbl.remove visited id_proc) ids;
	  print_ands (List.tl ids) (List.tl params) (List.tl ps) visited)

(*** Prints the declared processes to stdout ***)
	  
let print_procs () =
  print_procs_aux (!printprocs) (Hashtbl.create (List.length !printprocs))

(***)

(* Auxiliar functions to print_proc *)

let rec print_proc_ands id_proc idL paramL pL =
  match idL with
    [] -> false
  | hd::tl -> 
      if hd = id_proc then
	(print_string ("\ndefproc "^hd);
	 if (List.length (List.hd paramL)) > 0 then
	   (print_string "(";
	    print_names (List.hd paramL);
	    print_string ")");
	 print_string " = ";
	 print_ast (List.hd pL);
	 print_newline();
	 true)
      else
	print_proc_ands id_proc tl (List.tl paramL) (List.tl pL)

let rec print_proc_aux id_proc l =
  match l with
    [] -> false
  | (id,dec)::tl -> 
      if id = id_proc then
	(match dec with Pidec(ids, params, ps) ->
	  print_string ("\ndefproc "^id);
	  if List.length (List.hd params) > 0 then
	    (print_string "(";
	     print_names (List.hd params);
	     print_string ")");
	  print_string " = ";
	  print_ast (List.hd ps);
	  print_newline();
	  true)
      else
	(match dec with Pidec(ids,params,ps) ->
	  if print_proc_ands id_proc (List.tl ids) (List.tl params) (List.tl ps) then
	    true
	  else
	    print_proc_aux id_proc tl)

(* Prints a process to stdout given it's identifier *)

let print_proc id =
  print_proc_aux id !printprocs

let rec print_ids l =
match l with [] -> print_string ""
| hd::[] -> print_string (hd^",")
| hd::tl -> print_string (hd^","); print_ids tl

let rec print_ccproc id_proc l =
  match l with
    [] -> false
  | (id,args, ast)::tl -> 
      if id = id_proc then
	  (print_string ("\ndefproc cc "^id^"(");
	  print_ids args;
	  print_string ") = ";
	  print_newline();
	  print_ccast ast;
	  print_newline();
	  true)
      else
	(print_ccproc id_proc tl)


(***)

(* Auxiliar functions to install_proc *)

let defproc id nf =
  if (Hashtbl.mem !procs id) then 
    Hashtbl.replace !procs id nf
  else
    Hashtbl.add (!procs) id nf

let undefproc id =
  if (Hashtbl.mem !procs id) then
    Hashtbl.remove !procs id

let rec install_p idL paramL h =
  match idL with
    [] -> ignore idL
  | hd::tl ->
      defproc hd (normalform hd (List.hd paramL) h);
      install_p tl (List.tl paramL) h

let rec uninstall_p idL p_id =
  match idL with
    [] -> ignore idL
  | hd::tl ->
      if hd = p_id then
	ignore idL
      else
	(undefproc hd;
	 uninstall_p tl p_id)

(***)

let rec create_env h idL paramL pL =
  match idL with
    [] -> ignore idL
  | hd::tl ->
      if Hashtbl.mem !h hd then 
	Hashtbl.replace !h hd (List.hd paramL, List.hd pL)
      else
	Hashtbl.add (!h) hd (List.hd paramL , List.hd pL);
      create_env h tl (List.tl paramL) (List.tl pL)

let rec destroy_env h idL =
  match idL with
    [] -> ignore idL
  | hd::tl -> Hashtbl.remove !h hd; destroy_env h tl

(***)

let rec check_unguarded_ast ast env p_id visited =
  match !ast with
    Piastnode.Void -> 
      ignore ast
  | Piastnode.Par(p1,p2) ->
      check_unguarded_ast p1 env p_id visited;
      check_unguarded_ast p2 env p_id visited
  | Piastnode.Sum(p1,p2) ->
      ignore ast
  | Piastnode.New(nl,p) ->
      check_unguarded_ast p env p_id visited
  | Piastnode.Act(_,_) ->
      ignore ast
  | Piastnode.Test(id1,id2,p,typ) ->
      ignore ast
  | Piastnode.Var(id,al) ->
      if id = p_id then
	raise (UnguardedRec p_id)
      else
	(if not (Hashtbl.mem visited id) then
	  (try
	    let (pL,p) = Hashtbl.find !env id in
	    Hashtbl.add visited id true;
	    check_unguarded_ast p env p_id visited
	  with Not_found -> raise (Equations.UndeclaredId id)))
	  
let rec check_unguarded h idL size =
  match idL with
    [] -> ignore idL
  | hd::tl -> 
      let (pL,p) = Hashtbl.find !h hd in
      check_unguarded_ast p h hd (Hashtbl.create size);
      check_unguarded h tl size

(*** Installs the process declaration ***)

let rec install_proc proc =
  match proc with PIProcdec(Pidec(ids,params,ps)) ->
    create_env astprocs ids params ps;
    (try
      check_unguarded astprocs ids (List.length ids)
    with
      UnguardedRec(x) -> (destroy_env astprocs ids; raise (UnguardedRec x))
    | Equations.UndeclaredId(x) -> (destroy_env astprocs ids; raise (Equations.UndeclaredId x)));
    (try
      install_p ids params astprocs
    with 
      Equations.WrongNumArgs(x) ->
	(destroy_env astprocs ids; 
	 uninstall_p ids x;
	 raise (Equations.WrongNumArgs x))
    | Equations.UndeclaredId(x) -> 
	(destroy_env astprocs ids;
	 uninstall_p ids x;
	 raise (Equations.UndeclaredId x)));
    printprocs := (List.hd ids,Pidec(ids,params,ps))::!printprocs
| CCProcdec(Ccdec(id, args,ccproc)) ->
    let ccast = translate_ccast ccproc "up" "here" (Var(id,"up"::("here"::args))) in
    install_proc (PIProcdec(Pidec([id],["up"::("here"::args)],[ccast])));
    ccprocs := (id,args, ccproc)::!ccprocs


(***)

(* Auxiliar function to print_prop *) 
	
let rec print_props_aux l visited =
  match l with
    [] -> ignore l
  | (id,ns,ps,form)::tl ->
      if Hashtbl.mem visited id then
	print_props_aux tl visited
      else
	(Hashtbl.add visited id true;
	 print_props_aux tl visited;
	 print_string ("defprop "^id);
	 if (List.length ns > 0) || (List.length ps > 0) then
	   (print_string "(";
	    print_names ns;
	    if (List.length ns > 0) && (List.length ps > 0) then
	      print_string ", ";
	    print_names ps;
	    print_string ")");
	 print_string " = ";
	 print_form form;
	 print_string ";\n")

(*** Prints the declared formulas to stdout ***)

let print_props () =
  print_props_aux (!printforms) (Hashtbl.create (List.length !printforms))

(***)

(* Auxiliar function to print_prop *)

let rec print_prop_aux id_form l =
  match l with
    [] -> false
  | (id,ns,ps,form)::tl ->
      if (id = id_form) then
	(print_string ("\ndefprop "^id);
	 if (List.length ns > 0) || (List.length ps > 0) then
	   (print_string "(";
	    print_names ns;
	    if (List.length ns > 0) && (List.length ps > 0) then
	      print_string ", ";
	    print_names ps;
	    print_string ")");
	 print_string " = ";
	 print_form form;
	 print_newline();
	 true)
      else
	print_prop_aux id_form tl

(* Prints a formula to stdout given it's identifier *)

let print_prop id =
  print_prop_aux id !printforms

(***)

(* Auxiliar functions to install_prop *)

let rec install_list l nh =
  match l with
    [] -> []
  | hd::tl -> 
      if hd = "_" then hd::(install_list tl nh)
      else
      (try 
	   let r = Hashtbl.find (!nh) hd in
	   r::(install_list tl nh)
       with Not_found -> hd::(install_list tl nh))

let install_lab l nh =
  match l with
    OutLab(s,sl) -> 
      let ns = try Hashtbl.find (!nh) s with Not_found -> s in
      OutLab(ns, install_list sl nh)
  | InpLab(s,sl) -> 
      let ns = try Hashtbl.find (!nh) s with Not_found -> s in
      InpLab(ns, install_list sl nh)

let pv_init = "#X"
let pv_count = ref 0

let fresh_pvar () =
  let res = pv_init^(string_of_int !pv_count) in
  incr pv_count;
  res

let rec install_form form nh ph =
  match form with
    True -> True
  | False -> False
  | Void -> Void
  | NumComps(i,t) -> NumComps(i,t)
  | Eq(id1,id2) ->
      let nid1 = try Hashtbl.find (!nh) id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find (!nh) id2 with Not_found -> id2 in
      Eq(nid1,nid2)
  | Neq(id1,id2) -> 
      let nid1 = try Hashtbl.find (!nh) id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find (!nh) id2 with Not_found -> id2 in
      Neq(nid1,nid2)
  | Not(f) -> Not(install_form f nh ph)
  | And(f1,f2) -> And(install_form f1 nh ph, install_form f2 nh ph)
  | Or(f1,f2) -> Or(install_form f1 nh ph, install_form f2 nh ph)
  | Implies(f1,f2) -> Implies(install_form f1 nh ph, install_form f2 nh ph)
  | Equiv(f1,f2) -> Equiv(install_form f1 nh ph, install_form f2 nh ph)
  | Decomp(f1,f2) -> Decomp(install_form f1 nh ph, install_form f2 nh ph)
  | Comp(f1,f2) -> Comp(install_form f1 nh ph, install_form f2 nh ph)
  | Reveal(s,f) -> 
      let ns = try Hashtbl.find (!nh) s with Not_found -> s in
      Reveal(ns, install_form f nh ph)
  | RevealAll(s,f) -> 
      let ns = try Hashtbl.find (!nh) s with Not_found -> s in
      RevealAll(ns, install_form f nh ph)
  | Hidden(s,f) -> 
      Hashtbl.add (!nh) s s;
      let res = install_form f nh ph in
      Hashtbl.remove (!nh) s;
      Hidden(s,res)
  | Fresh(s,f) ->
      Hashtbl.add (!nh) s s;
      let res = install_form f nh ph in
      Hashtbl.remove (!nh) s;
      Fresh(s,res)
  | Free(s) ->
      let ns = try Hashtbl.find (!nh) s with Not_found -> s in
      Free(ns)
  | MayTau(f) -> MayTau(install_form f nh ph)
  | AllTau(f) -> AllTau(install_form f nh ph)
  | MayLab(l,f) -> MayLab(install_lab l nh, install_form f nh ph)
  | AllLab(l,f) -> AllLab(install_lab l nh, install_form f nh ph)
  | MayOutN(n,f) -> 
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      MayOutN(nn, install_form f nh ph)
  | MayInpN(n,f) ->
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      MayInpN(nn, install_form f nh ph)
  | AllOutN(n,f) ->
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      AllOutN(nn, install_form f nh ph)
  | AllInpN(n,f) ->
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      AllInpN(nn, install_form f nh ph)
  | MayOut(f) -> MayOut(install_form f nh ph)
  | MayInp(f) -> MayInp(install_form f nh ph)
  | AllOut(f) -> AllOut(install_form f nh ph)
  | AllInp(f) -> AllInp(install_form f nh ph)
  | MayN(n,f) -> 
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      MayN(nn, install_form f nh ph)
  | AllN(n,f) ->
      let nn = try Hashtbl.find (!nh) n with Not_found -> n in
      AllN(nn, install_form f nh ph)
  | May(f) -> May(install_form f nh ph)
  | All(f) -> All(install_form f nh ph)
  | Exists(n,f) ->
      Hashtbl.add (!nh) n n;
      let res = install_form f nh ph in
      Hashtbl.remove (!nh) n;
      Exists(n,res)
  | ForAll(n,f) ->
      Hashtbl.add (!nh) n n;
      let res = install_form f nh ph in
      Hashtbl.remove (!nh) n;
      ForAll(n,res)
  | MaxFix(x,params,f,args) ->
      let fpv = fresh_pvar() in
      Hashtbl.add (!ph) x (PropVar(fpv,[]));
      List.iter (fun id -> Hashtbl.add !nh id id) params;
      let res = install_form f nh ph in
      List.iter (fun id -> Hashtbl.remove !nh id) params;
      Hashtbl.remove (!ph) x;
      MaxFix(fpv,params,res,install_list args nh)
  | MinFix(x,params,f,args) ->
      let fpv = fresh_pvar() in
      Hashtbl.add (!ph) x (PropVar(fpv,[]));
      List.iter (fun id -> Hashtbl.add !nh id id) params;
      let res = install_form f nh ph in
      List.iter (fun id -> Hashtbl.remove !nh id) params;
      Hashtbl.remove (!ph) x;
      MinFix(fpv,params,res,install_list args nh)
  | Eventually(f) -> Eventually(install_form f nh ph)
  | Always(f) -> Always(install_form f nh ph)
  | Inside(f) -> Inside(install_form f nh ph)
  | Show_f(f) -> Show_f(install_form f nh ph)
  | Show_s(f) -> Show_s(install_form f nh ph)
  | PropVar(p,args) ->
      (try 
	let res = Hashtbl.find (!ph) p in
	(match res with
	  PropVar(pvarname,pvarargs) ->
	    (if List.length args > 0 then
	      PropVar(pvarname,install_list args nh)
	    else
	      res)
	| _ -> res)
      with
	Not_found -> raise Ill_formed_form)
  | Abbrev(id, args) ->
      raise Ill_formed_form

let rec add_names h pl al =
  match pl with
    [] -> ignore pl
  | hd::tl -> 
      Hashtbl.add (!h) hd (List.hd al);
      add_names h tl (List.tl al)

let rec extract_args args i len1 len2 =
  match args with
    [] -> if i <> (len1+len2) then raise (Wrong_args "Number of arguments and parameters differ!") else ([],[])
  | Abbrev(s,args)::tl ->
      let (r1,r2) = extract_args tl (i+1) len1 len2 in 
      if (i < len1) then 
	(if (List.length args) > 0 then raise (Wrong_args "Wrong kind of argument!") else (s::r1, r2))
      else
	(r1, Abbrev(s,args)::r2)
  | hd::tl ->
      if (i < len1) then raise (Wrong_args "Wrong kind of argument!") else 
      let (r1,r2) = extract_args tl (i+1) len1 len2 in
      (r1, hd::r2)

let rec install_defprop form ph =
  match form with
    True -> True
  | False -> False
  | Void -> Void
  | NumComps(i,t) -> NumComps(i,t)
  | Eq(id1,id2) -> Eq(id1,id2)
  | Neq(id1,id2) -> Neq(id1,id2)
  | Not(f) -> Not(install_defprop f ph)
  | And(f1,f2) -> And(install_defprop f1 ph, install_defprop f2 ph)
  | Or(f1,f2) -> Or(install_defprop f1 ph, install_defprop f2 ph)
  | Implies(f1,f2) -> Implies(install_defprop f1 ph, install_defprop f2 ph)
  | Equiv(f1,f2) -> Equiv(install_defprop f1 ph, install_defprop f2 ph)
  | Decomp(f1,f2) -> Decomp(install_defprop f1 ph, install_defprop f2 ph)
  | Comp(f1,f2) -> Comp(install_defprop f1 ph, install_defprop f2 ph)
  | Reveal(s,f) -> Reveal(s, install_defprop f ph)
  | RevealAll(s,f) -> RevealAll(s, install_defprop f ph)
  | Fresh(s,f) -> Fresh(s, install_defprop f ph)
  | Free(s) -> Free(s)
  | Hidden(s,f) -> Hidden(s, install_defprop f ph)
  | MayTau(f) -> MayTau(install_defprop f ph)
  | AllTau(f) -> AllTau(install_defprop f ph)
  | MayLab(l,f) -> MayLab(l, install_defprop f ph)
  | AllLab(l,f) -> AllLab(l, install_defprop f ph)
  | MayOutN(n,f) -> MayOutN(n, install_defprop f ph)
  | MayInpN(n,f) -> MayInpN(n, install_defprop f ph)
  | AllOutN(n,f) -> AllOutN(n, install_defprop f ph)
  | AllInpN(n,f) -> AllInpN(n, install_defprop f ph)
  | MayOut(f) -> MayOut(install_defprop f ph)
  | MayInp(f) -> MayInp(install_defprop f ph)
  | AllOut(f) -> AllOut(install_defprop f ph)
  | AllInp(f) -> AllInp(install_defprop f ph)
  | MayN(n,f) -> MayN(n,install_defprop f ph)
  | AllN(n,f) -> AllN(n,install_defprop f ph)
  | May(f) -> May(install_defprop f ph)
  | All(f) -> All(install_defprop f ph)
  | Exists(n,f) -> Exists(n, install_defprop f ph)
  | ForAll(n,f) -> ForAll(n, install_defprop f ph)
  | MaxFix(x,params,f,args) ->
      (if (List.length params) <> (List.length args) then
	raise (Wrong_args (x^": Number of arguments and parameters differ!")));
      Hashtbl.add (!ph) x (List.length params);
      let res = install_defprop f ph in
      Hashtbl.remove (!ph) x;
      MaxFix(x,params,res,args)
  | MinFix(x,params,f,args) -> 
      (if (List.length params) <> (List.length args) then
	raise (Wrong_args (x^": Number of arguments and parameters differ!")));
      Hashtbl.add (!ph) x (List.length params);
      let res = install_defprop f ph in
      Hashtbl.remove (!ph) x;
      MinFix(x,params,res,args)
  | Eventually(f) -> Eventually(install_defprop f ph)
  | Always(f) -> Always(install_defprop f ph)
  | Inside(f) -> Inside(install_defprop f ph)
  | Show_f(f) -> Show_f(install_defprop f ph)
  | Show_s(f) -> Show_s(install_defprop f ph)
  | PropVar(p,args) ->
      let npars = try Hashtbl.find (!ph) p with Not_found -> raise (Undeclared p) in
      if npars <> (List.length args) then 
	raise (Wrong_args (p^": Number of arguments and parameters differ!"))
      else 
	PropVar(p,args)
  | Abbrev(id, args) ->
      try
	let (nparaml, pparaml, f) = Hashtbl.find (!forms) id in
	let (nargs,pargs) = 
	  extract_args args 0 (List.length nparaml) (List.length pparaml) in
	let nameh = ref (Hashtbl.create (List.length nparaml)) in
	add_names nameh nparaml nargs;
	let proph = ref (Hashtbl.create (List.length pparaml)) in
	add_props proph pparaml pargs ph;
	install_form f nameh proph
      with 
	Not_found -> raise (Undeclared id)
      | Wrong_args(x) -> raise (Wrong_args (id^": "^x))

and add_props h pl al ph =
  match pl with
    [] -> ignore pl
  | hd::tl ->
      Hashtbl.add (!h) hd (install_defprop (List.hd al) ph);
      add_props h tl (List.tl al) ph

(***)

let defprop id nparaml pparaml f =
  let ph = ref (Hashtbl.create (List.length pparaml)) in
  List.iter (fun id -> Hashtbl.add (!ph) id 0) pparaml;
  let res = install_defprop f ph in
  if Hashtbl.mem !forms id then 
    Hashtbl.replace !forms id (nparaml, pparaml, res)
  else
    Hashtbl.add (!forms) id (nparaml, pparaml, res);
  printforms := (id,nparaml,pparaml,f)::!printforms

(*** Installs the formula declaration ***)

let install_prop dec =
  match dec with
    Dec((id, ns, ps),f) -> defprop id ns ps f

(***)

(* Auxiliar functions *)

let lab_aux p l env =
  match install_lab l env with 
    InpLab(s,sl) -> react p (Lab(Inp_type,s,sl))
  | OutLab(s,sl) -> react p (Lab(Out_type,s,sl))

let rec merge l1 l2 =
  match l2 with
    [] -> l1
  | hd::tl -> 
      if List.mem hd l1 then
	merge l1 tl
      else
	hd::(merge l1 tl)

let rec domain_form l pvarsL env =
  match pvarsL with
    [] -> l
  | hd::tl -> 
      let res = domain_form l tl env in
      try
	let (_,_,_,supp,_,_) = Hashtbl.find !env hd in
	merge res supp
      with Not_found -> res

let create_domains p f penv nenv =
  let fnp = free_names p in
  let (fnf_aux,pvars) = formFN f nenv in
  let fnf = domain_form fnf_aux pvars penv in
  let domain = fresh_name()::(merge fnf fnp) in
  (domain,fnp)

(***)

let rec fixpoint_args new_nenv params args =
  match params with
    [] -> ignore params
  | hd::tl -> 
      Hashtbl.add !new_nenv hd (List.hd args);
      fixpoint_args new_nenv tl (List.tl args)

let rec fixpoint_args_subst args nenv =
  match args with
    [] -> []
  | hd::tl -> 
      let nhd = try Hashtbl.find !nenv hd with Not_found -> hd in
      nhd::(fixpoint_args_subst tl nenv)

let rec arg_template args supp assocs =
  match args with
    [] -> ([],[])
  | hd::tl ->
      let (l1,l2) = arg_template tl supp assocs in
      if List.mem hd supp then
	(hd::l1,l2)
      else
	(let marker = try Hashtbl.find !assocs hd with Not_found -> gen_bname() in
	(marker::l1,hd::l2))

let rec match_template args template supp assocs =
  match template with
    [] -> (true,[])
  | hd::tl -> 
      let (ans,res) = match_template (List.tl args) tl supp assocs in
      if not ans then (false,[])
      else
	(if not (is_bname hd) then 
	  (hd = (List.hd args),res)
	 else
	  (if List.mem (List.hd args) supp then (false,[])
	   else
	     (let marker = 
	      try 
		Hashtbl.find !assocs (List.hd args) 
	      with Not_found -> (Hashtbl.add !assocs (List.hd args) hd; hd)
	     in
	     (marker = hd,(List.hd args)::res))))

(***)
	  
(* Model checker main algorithm *)

let rec check p form nenv penv =
  incr check_counter;
  (if (total_acts p > !max_threads) then
    raise MaxThreads);
  match form with
    True -> true
  | False -> false
  | Void -> empty_proc p
  | NumComps(i,t) ->
      (match t with
	EqNum -> 
	  if i = 1 then
	    (not (empty_proc p)) && ((num_comps p) = 1)
	  else
	    (num_comps p) = i
      | LtNum -> 
	  if i = 0 then
	    false
	  else if i = 1 then
	    empty_proc p
	  else
	    (num_comps p) < i
      | GtNum -> (not (empty_proc p)) && (num_comps p) > i)

      (***)

  | Eq(id1,id2) ->
      let nid1 = try Hashtbl.find (!nenv) id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find (!nenv) id2 with Not_found -> id2 in
      nid1 = nid2
  | Neq(id1,id2) ->
      let nid1 = try Hashtbl.find (!nenv) id1 with Not_found -> id1 in
      let nid2 = try Hashtbl.find (!nenv) id2 with Not_found -> id2 in
      nid1 <> nid2

      (***)

  | Not(f) -> not (check p f nenv penv)
  | And(f1,f2) -> (check p f1 nenv penv) && (check p f2 nenv penv)
  | Or(f1,f2) -> (check p f1 nenv penv) || (check p f2 nenv penv)
  | Implies(f1,f2) -> (not (check p f1 nenv penv)) || (check p f2 nenv penv)
  | Equiv(f1,f2) -> (((not (check p f1 nenv penv)) || (check p f2 nenv penv)) &&
		     ((not (check p f2 nenv penv)) || (check p f1 nenv penv)))

      (***)

  | Decomp(f1,f2) -> not (comp_aux p f1 f2 nenv penv false)
  | Comp(f1,f2) -> comp_aux p f1 f2 nenv penv true

      (***)

  | Reveal(s,f) ->
      let n = (try Hashtbl.find (!nenv) s with Not_found -> s) in
      reveal_aux p n f nenv penv true
  | RevealAll(s,f) ->
      let n = (try Hashtbl.find (!nenv) s with Not_found -> s) in
      not (reveal_aux p n f nenv penv false)
  | Fresh(s,f) ->
      let fresh = fresh_name() in
      Hashtbl.add (!nenv) s fresh;
      let res = check p f nenv penv in
      Hashtbl.remove (!nenv) s;
      res
  | Free(s) ->
      let n = (try Hashtbl.find (!nenv) s with Not_found -> s) in
      test_fn p n
  | Hidden(s,f) ->
      let fresh = fresh_name() in
      Hashtbl.add (!nenv) s fresh;
      let res = reveal_aux p fresh f nenv penv true in
      Hashtbl.remove (!nenv) s;
      res      
  
      (***)

  | MayTau(f) ->
      let tau_it = react p Tau in
      next_aux p tau_it f nenv penv true
  | AllTau(f) ->
      let tau_it = react p Tau in
      not (next_aux p tau_it f nenv penv false)
  
      (***)

  | MayLab(l,f) ->
      let lab_it = lab_aux p l nenv in
      next_aux p lab_it f nenv penv true
  | AllLab(l,f) ->
      let lab_it = lab_aux p l nenv in
      not (next_aux p lab_it f nenv penv false)
  
      (***)

  | MayOutN(n,f) -> 
      let nn = try Hashtbl.find (!nenv) n with Not_found -> n in
      let name_it = react p (Name(nn,Out_type)) in
      next_aux p name_it f nenv penv true
  | AllOutN(n,f) -> 
      let nn = try Hashtbl.find (!nenv) n with Not_found -> n in
      let name_it = react p (Name(nn,Out_type)) in
      not (next_aux p name_it f nenv penv false)
  | MayOut(f) -> 
      let action_it = react p (Action(Out_type)) in
      next_aux p action_it f nenv penv true
  | AllOut(f) -> 
      let action_it = react p (Action(Out_type)) in
      not (next_aux p action_it f nenv penv false)
  
      (***)

  | MayInpN(n,f) ->
      let (domain,_) = create_domains p (MayInpN(n,f)) penv nenv in
      let nn = try Hashtbl.find (!nenv) n with Not_found -> n in
      let lens = get_num_args p nn in
      may_iter_obj_aux p nn f nenv penv domain lens
  | AllInpN(n,f) -> 
      let (domain,_) = create_domains p (AllInpN(n,f)) penv nenv in
      let nn = try Hashtbl.find (!nenv) n with Not_found -> n in
      let lens = get_num_args p nn in
      all_iter_obj_aux p nn f nenv penv domain lens
  | MayInp(f) -> 
      let (domainObj, domainSub) = create_domains p f penv nenv in
      may_iter_sub_aux p f nenv penv domainSub domainObj
  | AllInp(f) ->
      let (domainObj, domainSub) = create_domains p f penv nenv in
      all_iter_sub_aux p f nenv penv domainSub domainObj

	(***)

  | MayN(n,f) ->
      (check p (MayOutN(n,f)) nenv penv) ||
      (check p (MayInpN(n,f)) nenv penv)
  | AllN(n,f) ->
      (check p (AllOutN(n,f)) nenv penv) &&
      (check p (AllInpN(n,f)) nenv penv)

	(***)

  | May(f) -> 
      (check p (MayTau(f)) nenv penv) || 
      (check p (MayOut(f)) nenv penv) || 
      (check p (MayInp(f)) nenv penv)
  | All(f) ->
      (check p (AllTau(f)) nenv penv) &&
      (check p (AllOut(f)) nenv penv) &&
      (check p (AllInp(f)) nenv penv)

	(***)

  | Exists(n,f) ->
      let (domain,_) = create_domains p (Exists(n,f)) penv nenv in
      iter_list_aux p n f nenv penv domain true
  | ForAll(n,f) ->
      let (domain,_) = create_domains p (ForAll(n,f)) penv nenv in
      iter_list_aux p n f nenv penv domain false

	(***)

  | MaxFix(x,params,f,args) -> 
      let (sf,nf_fns_aux,pvars) = subst (MaxFix(x,params,f,args)) nenv in
      (match sf with
	MaxFix(nx,nparams,nf,nargs) ->
          (let nf_fns = domain_form nf_fns_aux pvars penv in
	  let (template,marked) = arg_template nargs nf_fns (ref (Hashtbl.create 10)) in
          Hashtbl.add !penv nx (ref [(ref (create_pset p marked),template)],nf,nparams,nf_fns,Max,ref 0);
          let new_nenv = ref (Hashtbl.create 50) in
          fixpoint_args new_nenv nparams nargs;
          let res = check p nf new_nenv penv in
          Hashtbl.remove !penv nx;
          res)
      |	_ -> raise Ill_formed_form)
  | MinFix(x,params,f,args) ->
      let (sf, nf_fns_aux,pvars) = subst (MinFix(x,params,f,args)) nenv in
      (match sf with
	MinFix(nx,nparams,nf,nargs) ->
          (let nf_fns = domain_form nf_fns_aux pvars penv in
	  let (template,marked) = arg_template nargs nf_fns (ref (Hashtbl.create 10)) in
          Hashtbl.add !penv nx (ref [(ref (create_pset p marked),template)],nf,nparams,nf_fns,Min,ref 0);
          let new_nenv = ref (Hashtbl.create 50) in
          fixpoint_args new_nenv nparams nargs;
          let res = check p nf new_nenv penv in
          Hashtbl.remove !penv nx;
          res)
      | _ -> raise Ill_formed_form) 
  | PropVar(id,args) ->
      let (p_set_l,form,params,supp,fix_t,counter) = Hashtbl.find !penv id in
      let nargs = fixpoint_args_subst args nenv in
      let aux = ref (!p_set_l) in
      let not_done = ref true in
      let marked_args = ref [] in
      while !not_done && (List.length !aux > 0) do
	let (p_set, template) = List.hd !aux in
	let (found,marked) = 
	  if List.length nargs <> List.length template then 
	    (false,[])
	  else
	    match_template nargs template supp (ref (Hashtbl.create 10)) 
	in
	if not found then
	  aux := List.tl !aux
	else
	  (not_done := false; marked_args := marked)
      done;
      if !not_done then
	(let (template,marked) = arg_template nargs supp (ref (Hashtbl.create 10)) in
	 let n_pset = ref (create_pset p marked) in
	 p_set_l := (n_pset,template)::!p_set_l;
	 incr counter;
	 (if !trace_value then
	   (print_string ("Unfolding...\n");flush stdout));
         let new_nenv = ref (Hashtbl.create 50) in
         fixpoint_args new_nenv params nargs;
	 let res_check = check p form new_nenv penv in
	 decr counter;
	 (if (((not res_check) && (fix_t = Max)) 
	    || (res_check && (fix_t = Min))) then 
	   remove_from_pset !n_pset p marked);
	 res_check)
      else
	(let (p_set, template) = List.hd !aux in
	 if exists_congruent_n p !marked_args !p_set supp then
	   ((if !trace_value then
	     (print_string ("Found after "^
			    (string_of_int (!counter))^" steps!\n"); flush stdout));
	    match fix_t with
	      Max -> true
	    | Min -> false)
	 else
	   (add_to_pset !p_set p !marked_args;
	    incr counter;
	    (if !trace_value then
	      (print_string ("Unfolding...\n");flush stdout));
            let new_nenv = ref (Hashtbl.create 50) in
            fixpoint_args new_nenv params nargs;
	    let res_check = check p form new_nenv penv in
	    decr counter;
	    (if (((not res_check) && (fix_t = Max)) 
	       || (res_check && (fix_t = Min))) then 
	      remove_from_pset !p_set p !marked_args);
	    res_check))

	  (***)
	  
  | Eventually(f) ->
      let x = fresh_pvar() in
      check p (MinFix(x,[],Or(f,MayTau(PropVar(x,[]))),[])) nenv penv
  | Always(f) ->
      let x = fresh_pvar() in
      check p (MaxFix(x,[],And(f,AllTau(PropVar(x,[]))),[])) nenv penv

	  (***)

  | Inside(f) ->
      let p_res = ref p in
      let i = ref (find_rests !p_res) in
      while !i <> -1 do
	p_res := rev_comps !p_res !i 0 (fresh_name());
	i := find_rests !p_res
      done;
      check !p_res f nenv penv
    
	  (***)

  | Show_f(f) ->
      let res = check p f nenv penv in
      if not res then
	(print_string "\n> FAILS: The following process <\n"; 
	 print_process p;
	 print_string "> does not satisfy ";
	 print_form_subst f nenv;
	 print_string " <\n";
	 incr show_counter;
	 print_string "> Number of hits: "; 
	 print_int !show_counter;
	 print_string " <\n(press return to continue)";
	 let s = read_line() in
	 ignore s);
      res
  | Show_s(f) ->
      let res = check p f nenv penv in
      if res then
	(print_string "\n> SUCCEEDS: The following process <\n"; 
	 print_process p;
	 print_string "> satisfies ";
	 print_form_subst f nenv;
	 print_string " <\n";
	 incr show_counter;
	 print_string "> Number of hits: "; 
	 print_int !show_counter;
	 print_string " <\n(press return to continue)";
	 let s = read_line() in
	 ignore s);
      res

	(***)

  | Abbrev(_) ->
      raise Ill_formed_form

(* Auxiliar function that handles composition iteration *)

and comp_aux p f1 f2 nenv penv flag = 
  let comp_it = comp p in
  let res = ref false in
  (try
    while not !res do
      let (p1,p2) = next_comp comp_it in
      if flag then
	(if (check p1 f1 nenv penv) && (check p2 f2 nenv penv) then
	  res := true)
      else
	(if (not (check p1 f1 nenv penv)) && (not (check p2 f2 nenv penv)) then
	  res := true)
    done;
  with No_more_comps -> ignore "");
  !res

(* Auxiliar function that handles revelation iteration *)

and reveal_aux p n f nenv penv flag =
  let rev_it = reveal p n in
  let res = ref false in
  (try
    while not !res do
      let proc = next_reveal rev_it in
      if flag then
	(if check proc f nenv penv then
	  res := true)
      else
	(if not (check proc f nenv penv) then
	  res := true)
    done;
  with No_more_reveals -> ignore "");
  !res      

(* Auxiliar functions that handle the behavioral iterators *)

and next_aux p it f nenv penv flag =
  let res = ref false in
  (try 
    while not !res do
      let proc = next_react it in
      if flag then
	(if check proc f nenv penv then
	  res := true)
      else
	(if not (check proc f nenv penv) then
	  res := true)
    done;
  with No_more_reacts -> ignore "");
  !res

and may_iter_obj_aux p n f nenv penv domain lens = 
  match lens with
    [] -> false
  | hd::tl -> 
      let res = 
	if hd = 0 then
	  (may_iter_obj_args_aux p n f nenv penv [] 0 [])
	else
	  (may_iter_obj_lens_aux p n f nenv penv domain domain hd [])
      in
      if res then
	true
      else
	may_iter_obj_aux p n f nenv penv domain tl

and may_iter_obj_lens_aux p n f nenv penv dom1 dom2 len args =
  match dom1 with 
    [] -> false
  | hd::tl ->
      if may_iter_obj_args_aux p n f nenv penv dom2 (len-1) (hd::args) then
	true 
      else
	may_iter_obj_lens_aux p n f nenv penv tl dom2 len args

and may_iter_obj_args_aux p n f nenv penv dom len args =	
  if len = 0 then
    (let lab = Lab(Inp_type,n,args) in
    let lab_it = react p lab in
    next_aux p lab_it f nenv penv true)
  else
    may_iter_obj_lens_aux p n f nenv penv dom dom len args

and all_iter_obj_aux p n f nenv penv domain lens = 
  match lens with
    [] -> true
  | hd::tl -> 
      let res = 
	if hd = 0 then
	  (all_iter_obj_args_aux p n f nenv penv [] 0 [])
	else
	  (all_iter_obj_lens_aux p n f nenv penv domain domain hd [])
      in
      if not res then
	false
      else
	all_iter_obj_aux p n f nenv penv domain tl

and all_iter_obj_lens_aux p n f nenv penv dom1 dom2 len args =
  match dom1 with 
    [] -> true
  | hd::tl ->
      if not (all_iter_obj_args_aux p n f nenv penv dom2 (len-1) (hd::args)) then
	false
      else
	all_iter_obj_lens_aux p n f nenv penv tl dom2 len args 

and all_iter_obj_args_aux p n f nenv penv dom len args =	
  if len = 0 then
    (let lab = Lab(Inp_type,n,args) in
    let lab_it = react p lab in
    not (next_aux p lab_it f nenv penv false))
  else
    all_iter_obj_lens_aux p n f nenv penv dom dom len args 

and may_iter_sub_aux p f nenv penv l obj =
  match l with
    [] -> false
  | hd::tl ->
      let lens = get_num_args p hd in
      if may_iter_obj_aux p hd f nenv penv obj lens then
	true
      else
	may_iter_sub_aux p f nenv penv tl obj

and all_iter_sub_aux p f nenv penv l obj =
  match l with
    [] -> true
  | hd::tl ->
      let lens = get_num_args p hd in
      if not (all_iter_obj_aux p hd f nenv penv obj lens) then
	false
      else
	all_iter_sub_aux p f nenv penv tl obj

(* Auxiliar function that handles name quantification iterators *)

and iter_list_aux p n f nenv penv l flag = 
  match l with
    [] -> not flag
  | hd::tl -> 
      Hashtbl.add (!nenv) n hd;
      let res = check p f nenv penv in
      Hashtbl.remove (!nenv) n;
      if flag && res then
	true
      else if (not flag) && (not res) then
	false
      else
	iter_list_aux p n f nenv penv tl flag

(***)

(*** Calls the model checking procedure given a formula and a process identifier and arguments ***)

let top_check arg =
  match arg with (p_id,p_args,f) ->
    let nf = 
      try 
	Hashtbl.find !procs p_id 
      with Not_found -> raise (Equations.UndeclaredId p_id)
    in
    (match nf with (_,_,_,pars) -> 
      if (List.length p_args) <> (List.length pars) then
	raise (Wrong_args (p_id^": Number of arguments and parameters differ!")));
    (if (!trace_value) then
      print_nf nf);
    let proc = nf2process nf p_args in
    (if (!trace_value) then
      print_process proc);
    let nenv = ref (Hashtbl.create 0) in
    let prop = install_defprop f (nenv) in
    (if (!trace_value) then
      (print_string "\n*** PROPERTY ***\n";
       print_form prop;
       print_string "\n****************\n"));
    print_string "\nProcessing...\n";
    flush stdout;
    show_counter := 0;
    check_counter := 0;
    let tstart = Sys.time() in
    let r = check proc prop (ref (Hashtbl.create 50)) (ref (Hashtbl.create 20)) in
    let elapsed = Sys.time() -. tstart in
    (if (!show_time) then
      (print_string "\n- Time elapsed: ";
       print_float elapsed;
       print_string " secs -\n"));
    (if (!show_checkcounter) then
      (print_string "\n- Number of state visits: "; 
       print_int !check_counter;
       print_string " -\n"));
    print_string ("\n* Process "^p_id);
    if List.length p_args > 0 then
      (print_string "(";
       print_names p_args;
       print_string ")");
    if r then
      print_string " satisfies"
    else
      print_string " does not satisfy";
    print_string " the formula ";
    print_form f;
    if (!trace_value) then
      (print_string " *\n(press return to continue)";
       let s = read_line() in
       ignore s)
    else
      print_string " *\n"

(***)

(*** Clears all declarations ***)

let clear () =
  Hashtbl.clear !astprocs;
  printprocs := [];
  ccprocs := [];
  cdlspecs := [];
  Hashtbl.clear !procs;
  printforms := [];
  Hashtbl.clear !forms

(***)

(*** Updates the trace parameter value ***)
    
let trace arg =
  trace_value := arg

(***)

(*** Prints the trace parameter value ***)

let trace_val () =
  print_string ("\n- Trace option is ");
  if (!trace_value) then
    print_string "on -\n"
  else
    print_string "off -\n"

(***)

(*** Prints a process to stdout ***)

let show_proc id =
  print_string ("\n- Listing process "^id^" -\n");
  if not (print_ccproc id !ccprocs) then
     (if (not (print_proc id)) then
         print_string ("* NOT FOUND! *\n\n")
      else
         print_newline())
  else
    print_newline()

(***)

(*** Prints a formula to stdout ***)

let show_prop id =
  print_string ("\n- Listing formula "^id^" -\n");
  if not (print_prop id) then
    print_string ("* NOT FOUND! *\n\n")
  else
    print_newline()

(***)

(*** Updates the maxthreads parameter value ***)

let def_maxthreads new_mt =
  max_threads := new_mt

(***)

(*** Prints the maxthread parameter value ***)

let show_maxthreads () =
  print_string ("\n- Current value for max_threads is ");
  print_int !max_threads;
  print_string " -\n"

(***)

(*** Updates the checkcounter parameter value ***)

let def_checkcounter arg =
  show_checkcounter := arg

(***)

(*** Prints the checkcounter parameter value ***)

let checkcounter_val () =
  print_string ("\n- Parameter check_counter is ");
  if (!show_checkcounter) then
    print_string "on -\n"
  else
    print_string "off -\n"

(***)

(*** Updates the showtime parameter value ***)

let def_showtime arg =
  show_time := arg

(***)

(*** Prints the showtime parameter value ***)

let showtime_val () =
  print_string ("\n- Parameter show_time is ");
  if (!show_time) then
    print_string "on -\n"
  else
    print_string "off -\n"

(***)
