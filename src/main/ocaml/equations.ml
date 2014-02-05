(*** Module that handles the process equation system representation ***)

open Namegen
open Piastnode

(***)

exception Error
exception NameClash
exception WrongNumArgs of string
exception UndeclaredId of string

(***)

(*** Equation name type ***)

type eqname = 
    Fn of string
  | In of int
  | Rn of int
  | Pn of int

(*** Equation variable type ***)

type eqvar = int

(*** Action type ***)

type action_type = Out_type | Inp_type

(*** Action type ***)

type test_type = Equals_type | Differs_type

(*** Action prefix and continuation type ***)

type act = action_type * eqname * eqname list * eqvar * eqname list

(*** Internal action and continuation type ***)

type tau = eqvar * eqname list

(*** Test prefix and continuation type ***)

type test = test_type * eqname * eqname * eqvar * eqname list 

(*** Set of actions type ***)

type act_set = act array

(*** Set of tests type ***)

type test_set = test array

(*** Set of internal actions type ***)

type tau_set = tau array

(*** Sum type ***)

type sum = act list * tau list * test list

(*** Set of sums type ***)

type sum_set = sum list

(*** Equation type ***)

type equation =
    {num_pars: int;
     num_rests: int;
     num_fnouts: int;
     num_bnouts: int;
     num_fninps: int;
     num_bninps: int;
     num_tests: int;
     num_taus: int;
     fnouts: act_set;
     bnouts: act_set;
     fninps: act_set;
     bninps: act_set;
     tests: test_set;
     taus: tau_set;
     mutable sums: sum_set}

(*** Equation system type ***)

type eq_system = ((eqvar, equation) Hashtbl.t ref)

(*** Equation system free names type ***)

type eq_fns = ((eqvar, string list ref) Hashtbl.t ref)

(***)

(* Equation variables auxiliar functions *)

let eqvar_i = ref 1

let void_eqvar () = 0

let fresh_eqvar () = incr eqvar_i; (!eqvar_i-1)

(***)

(*** Tests if equation variable is the void variable ***)

let is_void_eqvar x = (x = 0)

(***)

(*** Empty equation constructor ***)

let nil_eq () = 
  {num_pars = 0;
   num_rests = 0; 
   num_fnouts = 0; 
   num_bnouts = 0; 
   num_fninps = 0; 
   num_bninps = 0;
   num_tests = 0;
   num_taus = 0;
   fnouts = [||]; 
   bnouts = [||]; 
   fninps = [||]; 
   bninps = [||];
   tests = [||];
   taus = [||];
   sums = []}

(***)

(*** Empty equation system constructor ***)

let nil_env () = ref (Hashtbl.create 0)

(***)

(*** Empty equation system free names constructor ***)

let nil_fns () = ref (Hashtbl.create 0)

(***)

(*** Returns the number of restrictions of the equation ***)

let count_rests eq = eq.num_rests

(***)

(*** Returns the number of parameters of the equation ***)

let count_pars eq = eq.num_pars

(***)

(*** Counts the number of actions of the equation ***)

let count_acts eq = 
  eq.num_fnouts + eq.num_fninps 
    + eq.num_bnouts + eq.num_bninps 
    + eq.num_tests + eq.num_taus + (List.length eq.sums)

(***)

(*** Prints equation variables ***)

let print_eqvar x = print_string "X"; print_int x

(***)

(* Auxiliar functions to print_nf *)

let print_eqname n =
  match n with
    Fn(n) -> print_string ("Fn("^n^")")
  | In(i) -> print_string ("In("); print_int i; print_string ")"
  | Rn(i) -> print_string ("Rn("); print_int i; print_string ")"
  | Pn(i) -> print_string ("Pn("); print_int i; print_string ")"

let rec print_list l =
  match l with
    [] -> ignore l
  | hd::[] -> print_eqname hd
  | hd::tl -> print_eqname hd; print_string ","; print_list tl

let print_act act = 
  match act with (t,sub,obj,var,args) ->
    print_eqname sub;
    (if (t = Out_type) then
	print_string "!("
    else
	print_string "?(");
    print_list obj;
    print_string ").";
    print_eqvar var;
    print_string "(";
    print_list args;
    print_string ")\n";
    var

let print_test test = 
  match test with (t,id1,id2,var,args) ->
    print_string "[";
    print_eqname id1;
    (if (t = Equals_type) then
      print_string "="
    else
      print_string "!=");
    print_eqname id2;
    print_string "].";
    print_eqvar var;
    print_string "(";
    print_list args;
    print_string ")\n";
    var

let print_tau tau = 
  match tau with (var,args) ->
    print_string "tau.";
    print_eqvar var;
    print_string "(";
    print_list args;
    print_string ")\n";
    var

let rec print_acts acts =
  match acts with
    [] -> []
  | hd::tl -> (print_act hd)::(print_acts tl)

let rec print_sum_acts act c =
  match act with
     [] -> ignore act
  | (hd::[]) -> c := (print_act hd)::!c
  | (hd::tl) -> c := (print_act hd)::!c; print_string "+ "; print_sum_acts tl c

let rec print_sum_taus tau c =
  match tau with
     [] -> ignore tau
  | (hd::[]) -> c := (print_tau hd)::!c
  | (hd::tl) -> c := (print_tau hd)::!c; print_string "+ "; print_sum_taus tl c

let rec print_sum_tests test c =
  match test with
     [] -> ignore test
  | (hd::[]) -> c := (print_test hd)::!c
  | (hd::tl) -> c := (print_test hd)::!c; print_string "+ "; print_sum_tests tl c

let rec print_sum s c =
  match s with
    (actList,tauList,testList) -> 
      print_sum_acts actList c; 
      (if (List.length actList > 0) && (List.length tauList > 0) then
	print_string "+ ");
      print_sum_taus tauList c;
      (if (List.length actList + List.length tauList > 0) && (List.length testList > 0) then
	print_string "+ ");
      print_sum_tests testList c

let rec print_sums sums c = 
  match sums with
    [] -> ignore sums
  | hd::[] -> print_sum hd c
  | hd::tl -> print_sum hd c; print_newline(); print_sums tl c

let print_eq eq = 
  print_string "- #pars: ";
  print_int (count_pars eq);
  print_newline();
  print_string "- #rests: ";
  print_int (count_rests eq);
  print_newline();
  print_string "- fnouts:\n";
  let c = ref [] in
  for i = 0 to eq.num_fnouts-1 do
    c := (print_act eq.fnouts.(i))::!c
  done;
  print_string "- bnouts:\n";
  for i = 0 to eq.num_bnouts-1 do
    c := (print_act eq.bnouts.(i))::!c
  done;  
  print_string "- fninps:\n";
  for i = 0 to eq.num_fninps-1 do
    c := (print_act eq.fninps.(i))::!c
  done;
  print_string "- bninps:\n";
  for i = 0 to eq.num_bninps-1 do
    c := (print_act eq.bninps.(i))::!c
  done;
  print_string "- tests:\n";
  for i = 0 to eq.num_tests-1 do
    c := (print_test eq.tests.(i))::!c
  done;
  print_string "- taus:\n";
  for i = 0 to eq.num_taus-1 do
    c := (print_tau eq.taus.(i))::!c
  done;
  print_string "- sums:\n";
  print_sums eq.sums c;
  !c

let rec print_nf_aux s l h =
  match l with
    [] -> ignore l
  | x::tl -> 
      if Hashtbl.mem h x then
	print_nf_aux s tl h
      else
	(Hashtbl.add h x 0;
	 let (eq) = Hashtbl.find !s x in
	 print_string ("\n*** X"^(string_of_int x)^" ***\n");
	 let c = print_eq eq in
	 print_string ("******\n");
	 print_nf_aux s (List.append c tl) h)
	
(*** Prints the equation system ***)

let print_nf nf =
  match nf with
    (s,f,x,args) -> 
      let done_vars = Hashtbl.create 100 in
      Hashtbl.add done_vars (void_eqvar()) 0;
      print_string "\n\n*** EQUATIONS ***\n";
      (if is_void_eqvar x then
	print_string ("\n*** EMPTY ***\n")
      else
	print_nf_aux s [x] done_vars);
      print_string "\n*****************\n\n"

(***)

(* Auxiliar functions to normalform *)

(* To handle substitution *)

let subst_name n subst_table =
  try 
    Hashtbl.find !subst_table n
  with Not_found -> n

let rec subst_list l subst_table =
  match l with
    [] -> []
  | hd::tl -> (subst_name hd subst_table)::(subst_list tl subst_table)

let rec subst_ast ast subst_table =
  match !ast with
    Void -> ref Void
  | Par(p1,p2) -> ref (Par(subst_ast p1 subst_table, subst_ast p2 subst_table))
  | Sum(p1,p2) -> ref (Sum(subst_ast p1 subst_table, subst_ast p2 subst_table))
  | New(nl,p) -> 
      let new_nl = ref [] in
      List.iter 
	(fun id -> let freshn = gen_bname() in 
	Hashtbl.add !subst_table id freshn; 
	new_nl := (freshn)::(!new_nl)) nl;
      let new_p = subst_ast p subst_table in
      List.iter (fun id -> Hashtbl.remove !subst_table id) nl;
      ref (New(!new_nl,new_p))
  | Act(t,p) ->
      (match t with
	Output(sub,obj) -> 
	  let new_sub = subst_name sub subst_table in
	  let new_obj = subst_list obj subst_table in
	  let new_p = subst_ast p subst_table in
	  ref (Act(Output(new_sub,new_obj),new_p))
      | Input(sub,obj) -> 
	  let new_sub = subst_name sub subst_table in
	  let new_obj = ref [] in
	  List.iter 
	    (fun id -> let freshn = gen_bname() in 
	    Hashtbl.add !subst_table id freshn; 
	    new_obj := List.append (!new_obj) [(freshn)]) obj;
	  let new_p = subst_ast p subst_table in
	  List.iter (fun id -> Hashtbl.remove !subst_table id) obj;
	  ref (Act(Input(new_sub,!new_obj),new_p))
      | Tau ->
	  let new_p = subst_ast p subst_table in
	  ref (Act(t,new_p)))
  | Test(id1,id2,p,typ) ->
      let nid1 = subst_name id1 subst_table in
      let nid2 = subst_name id2 subst_table in
      let newp = subst_ast p subst_table in
      ref (Test(nid1,nid2,newp,typ))
  | Var(x,al) -> ref (Var(x,subst_list al subst_table))

(***)

let rec sub_bound l env =
  match l with
    [] -> []
  | hd::tl -> 
      let new_n = gen_bname() in 
      Hashtbl.add !env hd new_n;
      (new_n)::(sub_bound tl env)

let rec sub_name n env =
  try 
    Hashtbl.find !env n
  with Not_found -> n

let rec sub_names l env =
  match l with
    [] -> []
  | hd::tl -> (sub_name hd env)::(sub_names tl env)

let rec sub_pars_aux pL aL env =
  match pL with
    [] -> ignore pL
  | hd::tl ->
      Hashtbl.add !env hd (List.hd aL);
      sub_pars_aux tl (List.tl aL) env

let sub_pars pL aL env new_env =
  let new_aL = sub_names aL env in
  sub_pars_aux pL new_aL new_env

(***)

(* To test if a process ast corresponds to the empty process *)

let rec test_void ast env =
  match !ast with
    Void -> true
  | Par(p1,p2) -> (test_void p1 env) && (test_void p2 env)
  | Sum(p1,p2) -> (test_void p1 env) && (test_void p2 env)
  | New(nl,p) -> (test_void p env)
  | Act(t,cont) -> false
  | Test(typ,id1,id2,cont) -> false
  | Var(id,al) ->
      let (pL,p) = 
	try
	  Hashtbl.find (!env) id 
	with Not_found -> raise (UndeclaredId id)
      in
      test_void p env

(***)

(* To obtain the set of top level restrictions, actions and sums out of a process ast *)

let rec normal_eq ast sub_env glob_env names =
  match !ast with
    Void -> ([],[],[])
  | Par(p1,p2) -> 
      let (rests1,acts1,sums1) = normal_eq p1 sub_env glob_env names in
      let (rests2,acts2,sums2) = normal_eq p2 sub_env glob_env names in
      (List.append rests2 rests1, List.append acts2 acts1, List.append sums2 sums1) 
  | Sum(p1,p2) ->
      let (rests1,acts1,sums1) = normal_eq p1 sub_env glob_env names in
      let (rests2,acts2,sums2) = normal_eq p2 sub_env glob_env names in
      if List.length rests1 <> 0 then
	raise Error;
      if List.length rests2 <> 0 then
	raise Error;
      if List.length sums2 <> 0 then
	raise Error;
      if List.length sums1 = 1 then
	([],[], [List.append acts2 (List.hd sums1)])
      else
	([],[], [List.append acts2 acts1])
  | New(l,p) ->
      let nl = sub_bound l sub_env in
      let (rests,acts,sums) = normal_eq p sub_env glob_env (List.append names nl) in
      List.iter (fun id -> Hashtbl.remove !sub_env id) l;
      (List.append nl rests, acts,sums)
  | Act(t,p) ->
      (match t with
	Output(sub,obj) ->
	  let nsub = sub_name sub sub_env in
	  let nobj = sub_names obj sub_env in
	  let np = 
	    if test_void p glob_env then (ref Void)
	    else subst_ast p sub_env in
	  ([],[(Act(Output(nsub,nobj),np),p,names)],[])
      | Input(sub,obj) ->
	  let nsub = sub_name sub sub_env in
	  let nobj = sub_bound obj sub_env in
	  let np = 
	    if test_void p glob_env then (ref Void)
	    else subst_ast p sub_env in
	  List.iter (fun id -> Hashtbl.remove !sub_env id) obj;
	  ([],[(Act(Input(nsub,nobj),np),p,List.append names nobj)],[])
      | Tau -> 
	  let np = 
	    if test_void p glob_env then (ref Void)
	    else subst_ast p sub_env in
	  ([],[(Act(Tau,np),p,names)],[]))
  | Test(id1,id2,p,typ) -> 
      let nid1 = sub_name id1 sub_env in
      let nid2 = sub_name id2 sub_env in
      let np = 
	if test_void p glob_env then
	  (ref Void)
	else
	  subst_ast p sub_env 
      in
      ([],[(Test(nid1,nid2,np,typ),p,names)],[])
  | Var(id,aL) ->
      (try
	let (pL,p) = 
	  try 
	    Hashtbl.find (!glob_env) id 
	  with Not_found -> raise (UndeclaredId id)
	in
	(if (List.length pL) <> (List.length aL) then
	  raise (WrongNumArgs (id^": Number of arguments and parameters differ!")));
	let sub_env_aux = ref (Hashtbl.create 100) in
	sub_pars pL aL sub_env sub_env_aux;
	let (rests,acts,sums) = normal_eq p sub_env_aux glob_env names in
	(rests,acts,sums)
      with Not_found -> raise Error)

(***)

(* To handle matching *)

let match_name n1 n2 old_args new_args bound =
  try
    let i = Hashtbl.find !old_args n1 in
    if (new_args.(i) <> "") && (new_args.(i) <> n2) then
      raise NameClash
    else
      new_args.(i) <- n2
  with Not_found ->
    (if (not (Hashtbl.mem !bound n1)) && (n1 <> n2) then raise NameClash)

let rec match_nameL l1 l2 old_args new_args bound =
  match l1 with
    [] -> (match l2 with [] -> ignore l1 | hd::tl -> raise Error)
  | hd1::tl1 -> 
      (match l2 with [] -> raise Error 
      | hd2::tl2 -> 
	  match_name hd1 hd2 old_args new_args bound;
	  match_nameL tl1 tl2 old_args new_args bound)

let rec match_args_aux c1 c2 old_args new_args bound =
  match !c1 with
    Void -> ignore c1
  | Par(p1,p2) ->
      (match !c2 with
	Par(q1,q2) -> 
	  match_args_aux p1 q1 old_args new_args bound;
	  match_args_aux p2 q2 old_args new_args bound
      | _ -> raise Error)
  | Sum(p1,p2) ->
      (match !c2 with
	Sum(q1,q2) ->
	  match_args_aux p1 q1 old_args new_args bound;
	  match_args_aux p2 q2 old_args new_args bound
      | _ -> raise Error)
  | New(nl1,p) ->
      (match !c2 with 
	New(nl2,q) -> 
	  List.iter (fun id -> Hashtbl.add !bound id 0) nl1;
	  match_args_aux p q old_args new_args bound;
	  List.iter (fun id -> Hashtbl.remove !bound id) nl1
      | _ -> raise Error)
  | Act(t1,p) ->
      (match !c2 with
	Act(t2,q) ->
	  (match t1 with
	    Output(s1,o1) -> 
	      (match t2 with 
		Output(s2,o2) -> 
		  match_name s1 s2 old_args new_args bound;
		  match_nameL o1 o2 old_args new_args bound;
		  match_args_aux p q old_args new_args bound
	      | _ -> raise Error)
	  | Input(s1,o1) -> 
	      (match t2 with
		Input(s2,o2) ->
		  match_name s1 s2 old_args new_args bound;
		  (List.iter (fun id -> Hashtbl.add !bound id 0) o1);
		  match_args_aux p q old_args new_args bound;
		  (List.iter (fun id -> Hashtbl.remove !bound id) o1)
	      | _ -> raise Error)
	  | Tau ->
	      if t2 <> t1 then raise Error else match_args_aux p q old_args new_args bound)
      | _ -> raise Error)
  | Test(n1,n2,p,t1) ->
      (match !c2 with
	Test(m1,m2,q,t2) ->
          if t2 <> t1 then raise Error else
	  (match_name n1 m1 old_args new_args bound;
	  match_name n2 m2 old_args new_args bound;
	  match_args_aux p q old_args new_args bound)
      | _ -> raise Error)
  | Var(id1,al1) ->
      (match !c2 with
	Var(id2,al2) ->
	  match_nameL al1 al2 old_args new_args bound
      | _ -> raise Error)

(***)

(* To determine if two process asts are the same up to a determined substitution *)

let match_args c1 n1 c2 =
  let args = ref (Hashtbl.create (List.length n1)) in
  let i = ref 0 in
  List.iter (fun id -> Hashtbl.add !args id !i; incr i) n1;
  let res = Array.create (List.length n1) "" in
  match_args_aux c1 c2 args res (ref (Hashtbl.create 50));
  for i = 0 to (Array.length res)-1 do
    if res.(i) = "" then
      res.(i) <- List.nth n1 i
  done;
  Array.to_list res

(***)

(* To determine if a process ast has already been visited *)

let rec visited el c ns l =
  match l with
    [] -> (false,void_eqvar(),[])
  | (ptr,var,names,cont)::tl -> 
      if ptr == el then
	(try
	  let new_args = match_args cont names c in
	  (true,var,new_args)
	with NameClash -> visited el c ns tl)
      else
	visited el c ns tl

(***)

(* To build the equation system action continuations *)

let rec treat_acts acts trail to_do =
  match acts with
    [] -> ([],[],[])
  | (Act(t,cont),cont_ref,names)::tl ->
      let (not_tau,typ,sub,obj) = 
	(match t with
		Output(s,o) -> (true,Out_type,s,o)
		| Input(s,o) -> (true,Inp_type,s,o)
		| Tau -> (false,Out_type, "", [])) in
      let (res_act,res_tau) =
	if !cont = Void then
	  ((typ,sub,obj,void_eqvar(),[]),(void_eqvar(),[]))
	else
	  (let (res,x,args) = visited cont_ref cont names !trail in
	  if res then
	    ((typ,sub,obj,x,args),(x,args))
	  else
	    (let freshx = fresh_eqvar() in
	    trail := (cont_ref,freshx,names,cont)::!trail;
	    to_do := (freshx,names,cont)::!to_do;
	    ((typ,sub,obj,freshx,names),(freshx,names))))
      in
      let (acts,tests,taus) = treat_acts tl trail to_do in
      if not_tau then
        (res_act::acts,tests,taus)
      else
        (acts,tests,res_tau::taus)
  | (Test(id1,id2,cont,typ),cont_ref,names)::tl ->
      let res_test =
	if !cont = Void then
	  (if (typ = Equals) then (Equals_type,id1,id2,void_eqvar(),[])
           else (Differs_type,id1,id2,void_eqvar(),[]))
	else
	  (let (res,x,args) = visited cont_ref cont names !trail in
	  if res then
            (if (typ = Equals) then (Equals_type,id1,id2,x,args)
             else (Differs_type,id1,id2,x,args))
	  else
	    (let freshx = fresh_eqvar() in
	    trail := (cont_ref,freshx,names,cont)::!trail;
	    to_do := (freshx,names,cont)::!to_do;
	    (if (typ = Equals) then (Equals_type,id1,id2,freshx,names)
             else (Differs_type,id1,id2,freshx,names))))
      in
      let (acts,tests,taus) = treat_acts tl trail to_do in
      (acts, res_test::tests,taus)
  | _ -> ([],[],[])

(***)

(* To build the equation system action continuations for sums *)

let rec treat_sums sums trail to_do =
  match sums with
    [] -> []
  | hd::tl -> 
      let (acts,tests,taus) = treat_acts hd trail to_do in
      (acts,taus,tests)::(treat_sums tl trail to_do)
			       
(***)

(* To handle equation building *)

let create_name n sub_env =
  try
    Hashtbl.find !sub_env n 
  with Not_found -> Fn(n)

let rec create_names nl sub_env =
  match nl with
    [] -> []
  | hd::tl -> (create_name hd sub_env)::(create_names tl sub_env)

let rec create_inp l i sub_env =
  match l with
    [] -> []
  | hd::tl -> 
      Hashtbl.add !sub_env hd (In(i));
      (In(i))::(create_inp tl (i+1) sub_env)

(***)

(* To build the actions considering a name substitution *)

let rec create_acts acts sub_env =
  match acts with
    [] -> ([],[],[],[])
  | (t,sub,obj,var,args)::tl ->
      let nsub = create_name sub sub_env in
      if t = Inp_type then
	(let nobj = create_inp obj 0 sub_env in
	let nargs = create_names args sub_env in
	List.iter (fun id -> Hashtbl.remove !sub_env id) obj;
	let (fnoL,bnoL,fniL,bniL) = create_acts tl sub_env in 
	(match nsub with
	  Rn(_) -> (fnoL,bnoL,fniL,(t,nsub,nobj,var,nargs)::bniL) 
	| _ -> (fnoL,bnoL,(t,nsub,nobj,var,nargs)::fniL,bniL)))
      else 
	(let nobj = create_names obj sub_env in
	let nargs = create_names args sub_env in
	let (fnoL,bnoL,fniL,bniL) = create_acts tl sub_env in
	(match nsub with
	  Rn(_) -> (fnoL,(t,nsub,nobj,var,nargs)::bnoL,fniL,bniL)
	| _ -> ((t,nsub,nobj,var,nargs)::fnoL,bnoL,fniL,bniL)))

(***)

(* To build the sums actions considering a name substitution *)

let rec create_acts_sums acts sub_env =
  match acts with
    [] -> ([])
  | (t,sub,obj,var,args)::tl ->
      let nsub = create_name sub sub_env in
      if t = Inp_type then
	(let nobj = create_inp obj 0 sub_env in
	let nargs = create_names args sub_env in
	List.iter (fun id -> Hashtbl.remove !sub_env id) obj;
	(t,nsub,nobj,var,nargs)::(create_acts_sums tl sub_env))
      else 
	(let nobj = create_names obj sub_env in
	let nargs = create_names args sub_env in
	(t,nsub,nobj,var,nargs)::(create_acts_sums tl sub_env))

(***)

(* To build the tests considering a name substitution *)

let rec create_tests tests sub_env =
  match tests with
    [] -> []
  | (typ,id1,id2,var,args)::tl ->
      let nid1 = create_name id1 sub_env in
      let nid2 = create_name id2 sub_env in
      let nargs = create_names args sub_env in
      (typ,nid1,nid2,var,nargs)::(create_tests tl sub_env)

(***)

(* To build the internal actions considering a name substitution *)

let rec create_taus taus sub_env =
  match taus with
    [] -> []
  | (var,args)::tl ->
      let nargs = create_names args sub_env in
      (var,nargs)::(create_taus tl sub_env)

(***)

(* To build sums considering a name substitution *)

let rec create_sums sums sub_env =
  match sums with
    [] -> []
  | hd::tl -> 
      match hd with (actL,tauL,testL) ->
	let acts = create_acts_sums actL sub_env in
	let taus = create_taus tauL sub_env in
	let tests = create_tests testL sub_env in
	(acts,taus,tests)::(create_sums tl sub_env)

(***)

(* To build an equation *)

let create_eq pars rests acts tests taus sums =
  let sub_env = ref (Hashtbl.create 100) in
  let i = ref 0 in
  List.iter (fun id -> Hashtbl.add !sub_env id (Pn(!i)); incr i) pars;
  i := 0;
  List.iter (fun id -> Hashtbl.add !sub_env id (Rn(!i)); incr i) rests;
  let (fnoL,bnoL,fniL,bniL) = create_acts acts sub_env in
  let res_taus = create_taus taus sub_env in
  let res_tests = create_tests tests sub_env in
  let res_sums = create_sums sums sub_env in
  {num_pars = (List.length pars); num_rests = (List.length rests);
   num_fnouts = List.length fnoL; num_bnouts = (List.length bnoL);
   num_fninps = List.length fniL; num_bninps = (List.length bniL);
   num_tests = List.length res_tests; num_taus = List.length res_taus;
   fnouts = Array.of_list fnoL; bnouts = Array.of_list bnoL;
   fninps = Array.of_list fniL; bninps = Array.of_list bniL;
   tests = Array.of_list res_tests; taus = Array.of_list res_taus; sums = res_sums}

(***)

(* To build the equation system *)

let rec normalform_aux glob_env sys trail to_do =
  match !to_do with 
    [] -> ignore to_do
  | (x,names,p)::tl ->
      let new_to_do = ref tl in
      let sub_env = ref (Hashtbl.create 100) in
      let (rests,acts,sums) = normal_eq p sub_env glob_env names in
      let (res_acts,res_tests,res_taus) = treat_acts acts trail new_to_do in
      let res_sums = treat_sums sums trail new_to_do in
      let eq = create_eq names rests res_acts res_tests res_taus res_sums in
      Hashtbl.add !sys x eq;
      normalform_aux glob_env sys trail (new_to_do)

(***)

(* To handle relevant parameters *)

(* To create the relevant parameter auxiliar tables *)

let rec create_relevs sys relevs x =
  if (not (is_void_eqvar x)) && (not (Hashtbl.mem !relevs x)) then
    (let eq = Hashtbl.find !sys x in
    Hashtbl.add !relevs x (Array.create (eq.num_pars) false);
    for i = 0 to eq.num_fnouts-1 do
      match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	create_relevs sys relevs cont
    done;
    for i = 0 to eq.num_bnouts-1 do
      match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	create_relevs sys relevs cont
    done;
    for i = 0 to eq.num_fninps-1 do
      match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	create_relevs sys relevs cont
    done;
    for i = 0 to eq.num_bninps-1 do
      match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	create_relevs sys relevs cont
    done;
    for i = 0 to eq.num_tests-1 do
      match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	create_relevs sys relevs cont
    done;
    for i = 0 to eq.num_taus-1 do
	match eq.taus.(i) with (cont,args) ->
	  create_relevs sys relevs cont
    done;
    List.iter 
      (fun l -> 
	match l with (acts,taus,tests) ->
	  (List.iter 
	    (fun act -> match act with (t,sub,obj,cont,args) 
	      -> create_relevs sys relevs cont) acts;
	  List.iter 
	    (fun tau -> match tau with (cont,args)
	      -> create_relevs sys relevs cont) taus;
	  List.iter
	    (fun test -> match test with (typ,id1,id2,cont,args) 
	      -> create_relevs sys relevs cont) tests))
      eq.sums)

(* To identify the relevant parameters *)

let mark_name n marker =
  (match n with
    Pn(i) -> 
      if not (marker.(i)) then 
	(marker.(i) <- true;
	 true)
      else
	false
  | _ -> false)

let rec mark_nameL l marker =
  match l with
    [] -> false
  | hd::tl -> 
      let res1 = (mark_name hd marker) in 
      let res2 = (mark_nameL tl marker) in
      res1 || res2

let rec mark_args l marker1 marker2 i =
  match l with
    [] -> false
  | hd::tl -> 
      let res1 = 
	if marker2.(i) then 
	  mark_name hd marker1 
	else 
	  false 
      in
      let res2 = (mark_args tl marker1 marker2 (i+1)) in
      res1 || res2

let rec mark_relevs sys relevs visited x =
  if (not (is_void_eqvar x)) && (not (Hashtbl.mem !visited x)) then
    (Hashtbl.add !visited x 0;
     let marker = Hashtbl.find !relevs x in
     let eq = Hashtbl.find !sys x in
     let changed = ref false in
     for i = 0 to eq.num_fnouts-1 do
       match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	 let res1 = mark_name sub marker in
	 let res2 = mark_nameL obj marker in
	 let res3 = 
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false 
	 in
	 changed := !changed || res1 || res2 || res3
     done;
     for i = 0 to eq.num_bnouts-1 do
       match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	 let res1 = mark_nameL obj marker in
	 let res2 =
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false
	 in
	 changed := !changed || res1 || res2	 
     done;
     for i = 0 to eq.num_fninps-1 do
       match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	 let res1 = mark_name sub marker in
	 let res2 =
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false
	 in
	 changed := !changed || res1 || res2
     done;
     for i = 0 to eq.num_bninps-1 do
       match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_tests-1 do
       match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	 let res1 = (mark_name id1 marker) || (mark_name id2 marker) in
	 let res2 = 
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false
	 in
	 changed := !changed || res1 || res2
     done;
     for i = 0 to eq.num_taus-1 do
       match eq.taus.(i) with (cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let marker2 = Hashtbl.find !relevs cont in
	     mark_args args marker marker2 0)
	   else
	     false
	 in
	 changed := !changed || res
     done;
     List.iter 
       (fun l -> 
	 match l with (acts,taus,tests) ->
	   (List.iter 
	      (fun act -> match act with (t,sub,obj,cont,args) -> 
		let res1 = mark_name sub marker in
		let res2 = 
		  if t = Inp_type then
		    false
		  else if t = Out_type then
		    mark_nameL obj marker 
		  else
	            false
		in
		let res3 =
		  if (not (is_void_eqvar cont)) then
		    (let marker2 = Hashtbl.find !relevs cont in
		    mark_args args marker marker2 0)
		  else
		    false
		in
		changed := !changed || res1 || res2 || res3) acts;
	    List.iter
	      (fun tau -> match tau with (cont,args) ->
		let res = 
	          if (not (is_void_eqvar cont)) then
		    (let marker2 = Hashtbl.find !relevs cont in
		    mark_args args marker marker2 0)
		  else
		    false
		in
		changed := !changed || res) taus;
	    List.iter 
	      (fun test -> match test with (typ,id1,id2,cont,args) ->
		let res1 = (mark_name id1 marker) || (mark_name id2 marker) in
		let res2 = 
		  if (not (is_void_eqvar cont)) then
		    (let marker2 = Hashtbl.find !relevs cont in
		    mark_args args marker marker2 0)
		  else
		    false
		in
		changed := !changed || res1 || res2) tests)) eq.sums;
     for i = 0 to eq.num_fnouts-1 do
       match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bnouts-1 do
       match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_fninps-1 do
       match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bninps-1 do
       match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_tests-1 do
       match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_taus-1 do
       match eq.taus.(i) with (cont,args) ->
	 let res = mark_relevs sys relevs visited cont in
	 changed := !changed || res
     done;
     List.iter (fun l -> match l with (acts,taus,tests) ->
       (List.iter 
	  (fun act -> match act with (t,sub,obj,cont,args) ->
	    let res = mark_relevs sys relevs visited cont in
	    changed := !changed || res) acts;
	List.iter
	  (fun tau -> match tau with (cont,args) ->
	    let res = mark_relevs sys relevs visited cont in
	    changed := !changed || res) taus;
	List.iter
	  (fun test -> match test with (typ,id1,id2,cont,args) ->
	    let res = mark_relevs sys relevs visited cont in
	    changed := !changed || res) tests)) eq.sums;
     !changed)
  else
    false

(* To clean up unnecessary data *)

let cleanup_name n new_params =
  match n with
    Pn(i) -> Pn(new_params.(i))
  | _ -> n

let rec cleanup_nameL l new_params =
  match l with
    [] -> []
  | hd::tl -> (cleanup_name hd new_params)::(cleanup_nameL tl new_params)

let rec cleanup_args l marker new_params i =
  match l with
    [] -> []
  | hd::tl ->
      if marker.(i) then
	(cleanup_name hd new_params)::(cleanup_args tl marker new_params (i+1))
      else
	cleanup_args tl marker new_params (i+1)

let cleanup_eq eq new_params relevs npars =
  let new_eq = 
    {num_pars = npars; num_rests = eq.num_rests;
     num_fnouts = eq.num_fnouts; num_bnouts = eq.num_bnouts;
     num_fninps = eq.num_fninps; num_bninps = eq.num_bninps; 
     num_tests = eq.num_tests; num_taus = eq.num_taus;
     fnouts = Array.create (eq.num_fnouts) (Out_type,Fn(""),[],void_eqvar(),[]);
     bnouts = Array.create (eq.num_bnouts) (Out_type,Fn(""),[],void_eqvar(),[]);
     fninps = Array.create (eq.num_fninps) (Inp_type,Fn(""),[],void_eqvar(),[]);
     bninps = Array.create (eq.num_bninps) (Inp_type,Fn(""),[],void_eqvar(),[]);
     tests = Array.create (eq.num_tests) (Equals_type,Fn(""),Fn(""),void_eqvar(),[]);
     taus = Array.create (eq.num_taus) (void_eqvar(),[]);
     sums = []}
  in
  for i = 0 to eq.num_fnouts-1 do
    match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
      let nsub = cleanup_name sub new_params in
      let nobj = cleanup_nameL obj new_params in
      let nargs = 
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.fnouts.(i) <- (t,nsub,nobj,cont,nargs)
  done;
  for i = 0 to eq.num_bnouts-1 do
    match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
      let nobj = cleanup_nameL obj new_params in
      let nargs = 
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.bnouts.(i) <- (t,sub,nobj,cont,nargs)
  done;
  for i = 0 to eq.num_fninps-1 do
    match eq.fninps.(i) with (t,sub,obj,cont,args) ->
      let nsub = cleanup_name sub new_params in
      let nargs = 
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.fninps.(i) <- (t,nsub,obj,cont,nargs)
  done;
  for i = 0 to eq.num_bninps-1 do
    match eq.bninps.(i) with (t,sub,obj,cont,args) ->
      let nargs =
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.bninps.(i) <- (t,sub,obj,cont,nargs)
  done;
  for i = 0 to eq.num_tests-1 do
    match eq.tests.(i) with (typ,id1,id2,cont,args) ->
      let nid1 = cleanup_name id1 new_params in
      let nid2 = cleanup_name id2 new_params in
      let nargs =
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.tests.(i) <- (typ,nid1,nid2,cont,nargs)
  done;
  for i = 0 to eq.num_taus-1 do
    match eq.taus.(i) with (cont,args) ->
      let nargs =
	if (not (is_void_eqvar cont)) then
	  (let marker = Hashtbl.find !relevs cont in
	  cleanup_args args marker new_params 0)
	else
	  []
      in
      new_eq.taus.(i) <- (cont,nargs)
  done;
  let new_sums = ref [] in
  List.iter (fun l -> 
    match l with (acts,taus,tests) ->
      (let new_acts = ref [] in
      List.iter 
	(fun act -> match act with (t,sub,obj,cont,args) ->
	  let nsub = cleanup_name sub new_params in
	  let nobj = 
	    if t = Inp_type then
	      obj
	    else if t = Out_type then
	      cleanup_nameL obj new_params 
	    else
	      obj
	  in
	  let nargs = 
	    if (not (is_void_eqvar cont)) then
	       (let marker = Hashtbl.find !relevs cont in
	       cleanup_args args marker new_params 0)
	     else
	       []
	   in
	   new_acts := (t,nsub,nobj,cont,nargs)::!new_acts) acts;
       let new_taus = ref [] in
       List.iter
	 (fun tau -> match tau with (cont,args) ->
	   let nargs = 
	     if (not (is_void_eqvar cont)) then
	       (let marker = Hashtbl.find !relevs cont in
	       cleanup_args args marker new_params 0)
	     else
	       []
	   in
	   new_taus := (cont,nargs)::!new_taus) taus;
       let new_tests = ref [] in
       List.iter
	 (fun test -> match test with (typ,id1,id2,cont,args) ->
	   let nid1 = cleanup_name id1 new_params in
	   let nid2 = cleanup_name id2 new_params in
	   let nargs =
	     if (not (is_void_eqvar cont)) then
	       (let marker = Hashtbl.find !relevs cont in
	       cleanup_args args marker new_params 0)
	     else
	       []
	   in
	   new_tests := (typ,nid1,nid2,cont,nargs)::!new_tests) tests;
       new_sums := (!new_acts,!new_taus,!new_tests)::!new_sums)) eq.sums;
  new_eq.sums <- !new_sums;
  new_eq

let rec cleanup_sys sys relevs visited x =
  if (not (is_void_eqvar x)) && (not (Hashtbl.mem !visited x)) then
    (Hashtbl.add !visited x 0;
     let marker = Hashtbl.find !relevs x in
     let eq = Hashtbl.find !sys x in
     Hashtbl.remove !sys x;
     let new_params = Array.create (eq.num_pars) (-1) in
     let pos = ref 0 in
     for i = 0 to eq.num_pars-1 do
       if marker.(i) then
	 (new_params.(i) <- !pos;
	  incr pos)
     done;
     let new_eq = cleanup_eq eq new_params relevs !pos in
     Hashtbl.add !sys x new_eq;
     for i = 0 to eq.num_fnouts-1 do
       match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     for i = 0 to eq.num_bnouts-1 do
       match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     for i = 0 to eq.num_fninps-1 do
       match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     for i = 0 to eq.num_bninps-1 do
       match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     for i = 0 to eq.num_tests-1 do
       match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     for i = 0 to eq.num_taus-1 do
       match eq.taus.(i) with (cont,args) ->
	 cleanup_sys sys relevs visited cont
     done;
     List.iter (fun l -> 
       match l with (acts,taus,tests) ->
	 (List.iter 
	    (fun act -> match act with (t,sub,obj,cont,args) ->
	      cleanup_sys sys relevs visited cont) acts;
	  List.iter
	    (fun tau -> match tau with (cont,args) ->
	      cleanup_sys sys relevs visited cont) taus;
	  List.iter
	    (fun test -> match test with (typ,id1,id2,cont,args) ->
	      cleanup_sys sys relevs visited cont) tests)) eq.sums)

(* To handle the relevant parameter identification procedure *)

let relevant_names sys entry =
  let relevs = ref (Hashtbl.create 100) in
  create_relevs sys relevs entry;
  let not_done = ref true in
  let visited = ref (Hashtbl.create 100) in
  while !not_done do
    (Hashtbl.clear !visited;
     not_done := mark_relevs sys relevs visited entry)
  done;
  Hashtbl.clear !visited;
  let eq = Hashtbl.find !sys entry in
  Hashtbl.replace !relevs entry (Array.make eq.num_pars true); 
  cleanup_sys sys relevs visited entry

(***)

(* To handle free name identification *)

let mark_fn_name n l =
  match n with 
    Fn(s) ->
      (if not (List.mem s !l) then
	l := s::!l)
  | _ -> ignore n

let rec mark_fn_nameL nL l =
  match nL with
    [] -> ignore nL
  | hd::tl -> 
      mark_fn_name hd l;
      mark_fn_nameL tl l

let rec create_fns sys fns x =
  if (not (is_void_eqvar x)) && (not (Hashtbl.mem !fns x)) then
    (let eq = Hashtbl.find !sys x in
    let fnL = ref [] in
    Hashtbl.add !fns x fnL;
    for i = 0 to eq.num_fnouts-1 do
      match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	mark_fn_name sub fnL;
	mark_fn_nameL obj fnL;
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    for i = 0 to eq.num_bnouts-1 do
      match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	mark_fn_nameL obj fnL;
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    for i = 0 to eq.num_fninps-1 do
      match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	mark_fn_name sub fnL;
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    for i = 0 to eq.num_bninps-1 do
      match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    for i = 0 to eq.num_tests-1 do
      match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	mark_fn_name id1 fnL;
	mark_fn_name id2 fnL;
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    for i = 0 to eq.num_taus-1 do
      match eq.taus.(i) with (cont,args) ->
	mark_fn_nameL args fnL;
	create_fns sys fns cont
    done;
    List.iter (fun l -> match l with (acts,taus,tests) ->
      (List.iter 
	 (fun act -> match act with (t,sub,obj,cont,args) ->
	   mark_fn_name sub fnL;
	   (if t = Out_type then mark_fn_nameL obj fnL);
	   mark_fn_nameL args fnL;
	   create_fns sys fns cont) acts;
       List.iter
	 (fun tau -> match tau with (cont,args) ->
	   mark_fn_nameL args fnL;
	   create_fns sys fns cont) taus;
       List.iter 
	 (fun test -> match test with (typ,id1,id2,cont,args) ->
	   mark_fn_name id1 fnL;
	   mark_fn_name id2 fnL;
	   mark_fn_nameL args fnL;
	   create_fns sys fns cont) tests)) eq.sums)

let rec mark_cont l1 l2 =
  match l1 with
    [] -> false
  | hd::tl -> 
      if List.mem hd !l2 then
	mark_cont tl l2
      else
	(l2 := hd::!l2; ignore (mark_cont tl l2); true)

let rec mark_fns sys fns visited x =
  if (not (is_void_eqvar x)) && (not (Hashtbl.mem !visited x)) then
    (Hashtbl.add !visited x 0;
     let fnL = Hashtbl.find !fns x in
     let eq = Hashtbl.find !sys x in
     let changed = ref false in
     for i = 0 to eq.num_fnouts-1 do
       match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false 
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bnouts-1 do
       match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false 
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_fninps-1 do
       match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false 
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bninps-1 do
       match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	 let res = 
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false 
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_tests-1 do
       match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	 let res =
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false
	 in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_taus-1 do
       match eq.taus.(i) with (cont,args) ->
	 let res =
	   if (not (is_void_eqvar cont)) then
	     (let fns_cont = Hashtbl.find !fns cont in
	     mark_cont !fns_cont fnL)
	   else
	     false
	 in
	 changed := !changed || res
     done;
     List.iter (fun l -> 
       match l with (acts,taus,tests) ->
	 (List.iter
	    (fun act -> match act with (t,sub,obj,cont,args) ->
	      let res = 
		if (not (is_void_eqvar cont)) then
		  (let fns_cont = Hashtbl.find !fns cont in
		  mark_cont !fns_cont fnL)
		else
		  false
	      in
	      changed := !changed || res) acts;
	  List.iter
	    (fun tau -> match tau with (cont,args) ->
	      let res = 
		if (not (is_void_eqvar cont)) then
		  (let fns_cont = Hashtbl.find !fns cont in
		  mark_cont !fns_cont fnL)
		else
		  false
	      in
	      changed := !changed || res) taus;
	  List.iter
	    (fun test -> match test with (typ,id1,id2,cont,args) ->
	      let res = 
		if (not (is_void_eqvar cont)) then
		  (let fns_cont = Hashtbl.find !fns cont in
		  mark_cont !fns_cont fnL)
		else
		  false
	      in
	      changed := !changed || res) tests)) eq.sums;
     for i = 0 to eq.num_fnouts-1 do
       match eq.fnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bnouts-1 do
       match eq.bnouts.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_fninps-1 do
       match eq.fninps.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_bninps-1 do
       match eq.bninps.(i) with (t,sub,obj,cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_tests-1 do
       match eq.tests.(i) with (typ,id1,id2,cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     for i = 0 to eq.num_taus-1 do
       match eq.taus.(i) with (cont,args) ->
	 let res = mark_fns sys fns visited cont in
	 changed := !changed || res
     done;
     List.iter (fun l -> match l with (acts,taus,tests) ->
       (List.iter
	  (fun act -> match act with (t,sub,obj,cont,args) ->
	    let res = mark_fns sys fns visited cont in
	    changed := !changed || res) acts;
	List.iter
	  (fun tau -> match tau with (cont,args) ->
	    let res = mark_fns sys fns visited cont in
	    changed := !changed || res) taus;
	List.iter
	  (fun test -> match test with (typ,id1,id2,cont,args) ->
	    let res = mark_fns sys fns visited cont in
	    changed := !changed || res) tests)) eq.sums;
     !changed)
  else
    false
     
(***)

(* To determine the set of free names associated with an equation system variable *)

let free_names sys entry =
  let fns = ref (Hashtbl.create 100) in
  create_fns sys fns entry;
  let not_done = ref true in
  let visited = ref (Hashtbl.create 100) in
  while !not_done do
    (Hashtbl.clear !visited;
     not_done := mark_fns sys fns visited entry)
  done;
  Hashtbl.clear !visited;
  fns

(***)

(*** Builds the equation system out of a Piastnode representation ***)

let normalform p_id p_args env =
  let sys = ref (Hashtbl.create 100) in
  let trail = ref [] in
  let x = fresh_eqvar() in
  let to_do = ref [(x,p_args,ref (Var(p_id,p_args)))] in
  normalform_aux env sys trail to_do;
  relevant_names sys x;
  let fns = free_names sys x in
  let eq = Hashtbl.find !sys x in
  if (count_acts eq = 0) then
    (nil_env(),nil_fns(),void_eqvar(),p_args)
  else
    (sys,fns,x,p_args)

(***)
