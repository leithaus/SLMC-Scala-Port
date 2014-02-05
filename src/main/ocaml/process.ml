(*** Module that handles the process top level representation ***)

open Namegen
open Piastnode
open Equations

(***)

exception False
exception Found
exception Error
exception Found_fn

(***)

(* Top level process name type *)

type name =
    Fname of string
  | Bname of string
  | Iname of int

(* Top level process action type *)

type top_act = {t: Equations.action_type; sub: name; obj: name list; cont: eqvar; args: name list}

(* Top level process action set type *)

type top_act_set = top_act array

(* Top level process internal action type *)

type top_tau = {tau_cont: eqvar; tau_args: name list}

(* Top level process internal action set type *)

type top_tau_set = top_tau array

(* Top level process test prefix type *)

type top_test = {tst: Equations.test_type; idl: name; idr: name; tcont: eqvar; targs: name list}

(* Top level process test prefix set type *)

type top_test_set = top_test array

(* Top level process sum type *)

type top_sum = (top_act list) * (top_tau list) * (top_test list)

(* Top level process sum set type *)

type top_sum_set = top_sum list

(* Top level process component type *)

type component = 
    {nrests: int;
     rests: name array;
     nfnouts: int;
     nbnouts: int;
     nfninps: int;
     nbninps: int;
     ntests: int;
     ntaus: int;
     nsums: int;
     fn_outs: top_act_set;
     bn_outs: top_act_set;
     fn_inps: top_act_set;
     bn_inps: top_act_set;
     id_tests: top_test_set;
     act_taus: top_tau_set;
     act_sums: top_sum_set}

(* Top level process structure type *)

type process_cel =  
    {n_comps: int;
     comps: component ref array;
     env: eq_system;
     fns: eq_fns}

(*** Top level process type ***)

type process = process_cel ref     

(***)

(* Action kind type *) 

type act_kind = ActK of top_act | TestK of top_test | SumK of top_sum | TauK of top_tau

(*** Top level process label type ***)

type label =  Equations.action_type * string * string list

(***)

(* Auxiliar functions to print_process *)

let print_name n =
  match n with
    Bname(s) -> print_string ("bn("^s^")")
  | Fname(s) -> print_string ("fn("^s^")")
  | Iname(i) -> print_string ("in("^(string_of_int i)^")")

let rec print_nameL l =
  match l with
    [] -> ignore l
  | hd::[] -> print_name hd
  | hd::tl -> print_name hd; print_string ","; print_nameL tl

let print_top_act act =
  print_name act.sub;
  (if (act.t = Out_type) then
    print_string "!("
  else
    print_string "?(");
  print_nameL act.obj;
  print_string ").";
  print_eqvar act.cont;
  print_string "(";
  print_nameL act.args;
  print_string ")\n"

let print_top_tau tau =
  print_string "tau.";
  print_eqvar tau.tau_cont;
  print_string "(";
  print_nameL tau.tau_args;
  print_string ")\n"

let print_top_test test =
  print_string "[";
  print_name test.idl;
  (if (test.tst = Equals_type) then
    print_string "="
  else 
    print_string "!=");
  print_name test.idr;
  print_string "].";
  print_eqvar test.tcont;
  print_string "(";
  print_nameL test.targs;
  print_string ")\n"

let rec print_top_acts_sum s =
  match s with
    [] -> ignore s
  | hd::[] -> print_top_act hd
  | hd::tl -> print_top_act hd; print_string "+ "; print_top_acts_sum tl

let rec print_top_taus_sum s =
  match s with
    [] -> ignore s
  | hd::[] -> print_top_tau hd
  | hd::tl -> print_top_tau hd; print_string "+ "; print_top_taus_sum tl

let rec print_top_tests_sum s =
  match s with
    [] -> ignore s
  | hd::[] -> print_top_test hd
  | hd::tl -> print_top_test hd; print_string "+ "; print_top_tests_sum tl

let rec print_top_sums sums =
  match sums with
    [] -> ignore sums
  | (acts,taus,tests)::[] -> 
      print_top_acts_sum acts;
      (if (List.length acts > 0) && (List.length taus > 0) then
	print_string "+ ");
      print_top_taus_sum taus;
      (if (List.length acts + List.length taus > 0) && (List.length tests > 0) then
	print_string "+ ");
      print_top_tests_sum tests;
  | (acts,taus,tests)::tl -> 
      print_top_acts_sum acts;
      (if (List.length acts > 0) && (List.length taus > 0) then
	print_string "+ ");
      print_top_taus_sum taus;
      (if (List.length acts + List.length taus > 0) && (List.length tests > 0) then
	print_string "+ ");
      print_top_tests_sum tests;
      print_newline(); 
      print_top_sums tl

(***)

let print_component comp =
  print_string "- COMP -\nrestricted: ";
  for i = 0 to !comp.nrests-1 do
    print_name (!comp.rests.(i));
    print_string " "
  done;
  print_string "\nfnouts: ";
  print_int !comp.nfnouts;
  print_newline();
  for i = 0 to !comp.nfnouts-1 do
    print_top_act (!comp.fn_outs.(i))
  done;
  print_string "fninps: ";
  print_int !comp.nfninps;
  print_newline();
  for i = 0 to !comp.nfninps-1 do
    print_top_act (!comp.fn_inps.(i))
  done;
  print_string "bnouts: ";
  print_int !comp.nbnouts;
  print_newline();
  for i = 0 to !comp.nbnouts-1 do
    print_top_act (!comp.bn_outs.(i))
  done;
  print_string "bninps: ";
  print_int !comp.nbninps;
  print_newline();
  for i = 0 to !comp.nbninps-1 do
    print_top_act (!comp.bn_inps.(i))
  done;
  print_string "taus: ";
  print_int !comp.ntaus;
  print_newline();
  for i = 0 to !comp.ntaus-1 do
    print_top_tau (!comp.act_taus.(i))
  done;
  print_string "tests: ";
  print_int !comp.ntests;
  print_newline();
  for i = 0 to !comp.ntests-1 do
    print_top_test (!comp.id_tests.(i))
  done;
  print_string "sums: ";
  print_int !comp.nsums;
  print_newline();
  print_top_sums !comp.act_sums

(*** Prints a top level process ***)

let print_process p =
  print_string "*** PROCESS ***\n";
  for i = 0 to (Array.length (!p.comps)) -1 do
    print_component (!p.comps.(i))
  done;
  print_string "***************\n"

(***)

(* Auxiliar functions *)

let fresh_rests size =
  let res = Array.create size "" in
  for i = 0 to (size)-1 do
    res.(i) <- gen_bname();
  done;
  res

(***)

let get_string n =
  match n with
    Bname(s) -> s
  | Fname(s) -> s
  | _ -> ""

let rec get_stringL nL =
  match nL with
    [] -> []
  | hd::tl -> (get_string hd)::(get_stringL tl)

(***)

let nil_component () = 
  {nrests = 0; 
   rests = [||]; 
   nfnouts = 0; 
   nbnouts = 0; 
   nfninps = 0; 
   nbninps = 0;
   ntests = 0;
   ntaus = 0;
   nsums = 0;
   fn_outs = [||]; 
   bn_outs = [||]; 
   fn_inps = [||]; 
   bn_inps = [||];
   id_tests = [||];
   act_taus = [||];
   act_sums = []}

(***)

let new_component rL fnoL bnoL fniL bniL tests taus sums =
  {nrests = List.length rL; 
   rests = Array.of_list rL; 
   nfnouts = List.length fnoL;
   nbnouts = List.length bnoL;
   nfninps = List.length fniL;
   nbninps = List.length bniL;
   ntests = List.length tests;
   ntaus = List.length taus;
   nsums = List.length sums;
   fn_outs = Array.of_list fnoL;
   bn_outs = Array.of_list bnoL;
   fn_inps = Array.of_list fniL;
   bn_inps = Array.of_list bniL;
   id_tests = Array.of_list tests;
   act_taus = Array.of_list taus;
   act_sums = sums}

(***)

(* Auxiliar functions to handle component identification *)

let rec get_comps a acts num_acts names num_names part j =
  for k = 0 to (num_acts) -1 do
    if acts.(k) = 0 && a.(k).(j) then
      (acts.(k) <- part;
       get_names a acts num_acts names num_names part k)
  done
and
get_names a acts num_acts names num_names part i =
  for j = 0 to (num_names)-1 do
    if names.(j) = 0 && a.(i).(j) then 
      (names.(j) <- part;
       get_comps a acts num_acts names num_names part j)   
  done

let comps a =
  let num_acts = Array.length a in
  let num_names = Array.length a.(0) in
  let parts = ref 1 in
  let acts = Array.create num_acts 0 in
  let names = Array.create num_names 0 in
  for i = 0 to num_acts-1 do
    if acts.(i) = 0 then      
      (acts.(i) <- !parts;
       get_names a acts num_acts names num_names !parts i;
       incr parts)
  done;
  (!parts-1,acts,names)

(***)

(* Auxiliar functions to handle top level process action creation *)

let eq_name n marker pos sub_args sub_rests pars_marker =
  match n with
    Rn(i) -> marker.(pos).(i) <- true; Bname(sub_rests.(i))
  | Pn(i) -> 
      (try 
	let k = Hashtbl.find !pars_marker (get_string sub_args.(i)) in 
	marker.(pos).(k) <- true
      with Not_found -> ignore i);
      sub_args.(i)
  | Fn(s) -> Fname(s)
  | In(i) -> Iname(i)

let rec eq_nameL l marker pos sub_args sub_rests pars_marker =
  match l with
    [] -> []
  | hd::tl -> 
      (eq_name hd marker pos sub_args sub_rests pars_marker)::
      (eq_nameL tl marker pos sub_args sub_rests pars_marker)

let eq_act act marker sub_args sub_rests pos pars_marker =
  match act with (eq_t,s,o,x,a) ->
    {t = eq_t;
     sub= eq_name s marker pos sub_args sub_rests pars_marker;
     obj= eq_nameL o marker pos sub_args sub_rests pars_marker;
     cont = x;
     args = eq_nameL a marker pos sub_args sub_rests pars_marker}

let eq_test test marker sub_args sub_rests pos pars_marker =
  match test with (typ,id1,id2,x,a) ->
    {tst = typ;
     idl= eq_name id1 marker pos sub_args sub_rests pars_marker;
     idr= eq_name id2 marker pos sub_args sub_rests pars_marker;
     tcont = x;
     targs = eq_nameL a marker pos sub_args sub_rests pars_marker}

let eq_tau tau marker sub_args sub_rests pos pars_marker =
  match tau with (x,a) ->
    {tau_cont = x;
     tau_args = eq_nameL a marker pos sub_args sub_rests pars_marker}

let eq_acts eq marker sub_args sub_rests start_act pars_marker start_outs start_inps start_tests start_taus start_sums =
  let outs = ref start_outs in
  let accum = ref start_act in
  for i = 0 to eq.num_fnouts-1 do
    outs := ((eq_act eq.fnouts.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!outs
  done;
  accum := !accum + eq.num_fnouts;
  for i = 0 to eq.num_bnouts-1 do
    outs := ((eq_act eq.bnouts.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!outs
  done;
  accum := !accum + eq.num_bnouts;
  let inps = ref start_inps in
  for i = 0 to eq.num_fninps-1 do
    inps := ((eq_act eq.fninps.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!inps
  done;
  accum := !accum + eq.num_fninps;
  for i = 0 to eq.num_bninps-1 do
    inps := ((eq_act eq.bninps.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!inps
  done;
  accum := !accum + eq.num_bninps;
  let tests = ref start_tests in
  for i = 0 to eq.num_tests-1 do
    tests := ((eq_test eq.tests.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!tests
  done;
  accum := !accum + eq.num_tests;
  let taus = ref start_taus in
  for i = 0 to eq.num_taus-1 do
    taus := ((eq_tau eq.taus.(i) marker sub_args sub_rests (!accum+i) pars_marker),(!accum+i))::!taus
  done;
  accum := !accum + eq.num_taus;
  let sums = ref start_sums in
  List.iter (fun l -> 
    match l with (s_acts,s_taus,s_tests) ->
    (let sum_acts = ref [] in
    List.iter 
      (fun act -> 
	sum_acts := (eq_act act marker sub_args sub_rests !accum pars_marker)::!sum_acts) s_acts;
    let sum_tests = ref [] in
    List.iter
      (fun test ->
	sum_tests := (eq_test test marker sub_args sub_rests !accum pars_marker)::!sum_tests) s_tests;
    let sum_taus = ref [] in
    List.iter
      (fun tau ->
	sum_taus := (eq_tau tau marker sub_args sub_rests !accum pars_marker)::!sum_taus) s_taus;
    sums := ((!sum_acts,!sum_taus,!sum_tests),!accum)::!sums; incr accum)) eq.sums;
  (outs,inps,tests,taus,sums)

(***)

(* Auxiliar functions to handle top level process component creation *)

let create_comps outs inps tests taus sums num_comps comp_acts =
  let res_fnos = Array.create num_comps ([]) in
  let res_bnos = Array.create num_comps ([]) in
  let res_fnis = Array.create num_comps ([]) in
  let res_bnis = Array.create num_comps ([]) in
  let res_tests = Array.create num_comps ([]) in
  let res_taus = Array.create num_comps ([]) in
  let res_sums = Array.create num_comps ([]) in
  let num_outs = List.length !outs in
  let num_inps = List.length !inps in
  let num_tests = List.length !tests in
  let num_taus = List.length !taus in
  for i = 0 to Array.length comp_acts-1 do
    if i < (num_outs+num_inps) then
      (let (act,act_pos,out) = 
	if i < num_outs then
	  let (res,act_pos) = List.hd !outs in outs := List.tl !outs; (res,act_pos,true)
	else 
	  let (res,act_pos) = List.hd !inps in inps := List.tl !inps; (res,act_pos,false)
      in
      let fn = match act.sub with Bname(s) -> false | _ -> true in
      if fn then
	(if out then
	  res_fnos.(comp_acts.(act_pos)-1) <- act::(res_fnos.(comp_acts.(act_pos)-1))
	else
	  res_fnis.(comp_acts.(act_pos)-1) <- act::(res_fnis.(comp_acts.(act_pos)-1)))
      else
	(if out then
	  res_bnos.(comp_acts.(act_pos)-1) <- act::(res_bnos.(comp_acts.(act_pos)-1))
	else
	  res_bnis.(comp_acts.(act_pos)-1) <- act::(res_bnis.(comp_acts.(act_pos)-1))))
    else if i < (num_outs+num_inps+num_tests) then
      (let (test,test_pos) = List.hd !tests in 
      tests := List.tl !tests;
      res_tests.(comp_acts.(test_pos)-1) <- test::(res_tests.(comp_acts.(test_pos)-1)))
    else if i < (num_outs+num_inps+num_tests+num_taus) then
      (let (tau,tau_pos) = List.hd !taus in
      taus := List.tl !taus;
      res_taus.(comp_acts.(tau_pos)-1) <- tau::(res_taus.(comp_acts.(tau_pos)-1)))
    else
      (let (sum,sum_pos) = List.hd !sums in
      sums := List.tl !sums;
      res_sums.(comp_acts.(sum_pos)-1) <- sum::(res_sums.(comp_acts.(sum_pos)-1)))
  done;
  (res_fnos, res_bnos, res_fnis, res_bnis, res_tests, res_taus, res_sums)

let eq_rests comp_names num_comps sub_rests size res_names start_pos =
  for i = 0 to size-1 do
    if (comp_names.(i+start_pos) <> 0) then
      res_names.(comp_names.(i+start_pos)-1) <- 
	Bname(sub_rests.(i))::(res_names.(comp_names.(i+start_pos)-1))
  done

(***)

(*** Creates a top level process from an equation system ***)

let nf2process nf args =
  match nf with (s,f,x,pars) ->
    if is_void_eqvar x then
      (let res = {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()} in
      ref res)
    else
      (let eq = Hashtbl.find !s x in
      let marker = Array.make_matrix (count_acts eq) (count_rests eq) false in
      let sub_args = Array.create (List.length args) (Fname("")) in
      let i = ref 0 in
      List.iter (fun s -> sub_args.(!i) <- Fname(s); incr i) args;
      let sub_rests = fresh_rests (count_rests eq) in
      let (outs,inps,tests,taus,sums) = eq_acts eq marker sub_args sub_rests 0 (ref (Hashtbl.create 0)) [] [] [] [] [] in
      let (num_comps, comp_acts, comp_names) = comps marker in
      let (fnoL,bnoL, fniL, bniL,id_ts,act_ts,act_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
      let rL = Array.create num_comps ([]) in
      eq_rests comp_names num_comps sub_rests (count_rests eq) rL 0;
      let res = {n_comps = num_comps; comps = Array.create num_comps (ref (nil_component())); env = s; fns = f} in
      for i = 0 to num_comps-1 do
	res.comps.(i) <- ref (new_component (rL.(i)) (fnoL.(i)) (bnoL.(i)) (fniL.(i)) (bniL.(i)) (id_ts.(i)) (act_ts.(i)) (act_ss.(i)))
      done;
      ref res)

(***)

(* Auxiliar functions to test_fn *)

let test_fn_name n arg =
  match n with
    Fname(s) -> s = arg
  | Bname(s) -> false
  | Iname(i) -> false

let rec test_fn_nameL l arg =
  match l with 
    [] -> false
  | hd::tl ->
      (test_fn_name hd arg) || (test_fn_nameL tl arg)

let test_fn_aux act n fnsub =
  (fnsub && (test_fn_name act.sub n)) ||
  ((act.t = Out_type) && (test_fn_nameL act.obj n)) ||
  (test_fn_nameL act.args n)

(*** Tests if a process has a determined free name ***)

let test_fn p n =
  let i = ref 0 in
  let j = ref 0 in
  let res = ref false in
  while (not !res) && (!i < !p.n_comps) do
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).nfnouts) do
      res := test_fn_aux !(!p.comps.(!i)).fn_outs.(!j) n true;
      res := !res || 
      (try
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).fn_outs.(!j).cont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).nfninps) do
      res := test_fn_aux !(!p.comps.(!i)).fn_inps.(!j) n true;
      res := !res || 
      (try
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).fn_inps.(!j).cont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).nbnouts) do
      res := test_fn_aux !(!p.comps.(!i)).bn_outs.(!j) n false;
      res := !res || 
      (try 
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).bn_outs.(!j).cont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).nbninps) do
      res := test_fn_aux !(!p.comps.(!i)).bn_inps.(!j) n false;
      res := !res || 
      (try
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).bn_inps.(!j).cont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).ntests) do
      res := test_fn_name !(!p.comps.(!i)).id_tests.(!j).idl n;
      res := (!res || (test_fn_name !(!p.comps.(!i)).id_tests.(!j).idr n));
      res := (!res || (test_fn_nameL !(!p.comps.(!i)).id_tests.(!j).targs n));
      res := !res || 
      (try
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).id_tests.(!j).tcont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    j := 0;
    while (not !res) && (!j < !(!p.comps.(!i)).ntaus) do
      res := test_fn_nameL !(!p.comps.(!i)).act_taus.(!j).tau_args n;
      res := !res || 
      (try
	let fnL = Hashtbl.find !(!p.fns) !(!p.comps.(!i)).act_taus.(!j).tau_cont in 
	List.mem n !fnL
      with Not_found -> false);
      incr j
    done;
    (try 
      (List.iter (fun sum -> match sum with (acts,taus,tests)->
	  (List.iter 
	    (fun act -> if !res then raise Found_fn;
	      res := (!res || (test_fn_aux act n true));
	      res := (!res || 
	        (try
	          let fnL = Hashtbl.find !(!p.fns) act.cont in 
	          List.mem n !fnL
	        with Not_found -> false))) acts;
	  List.iter
	    (fun tau -> if !res then raise Found_fn;
	       res := (!res || (test_fn_nameL tau.tau_args n));
	       res := (!res ||
	         (try
	           let fnL = Hashtbl.find !(!p.fns) tau.tau_cont in
	           List.mem n !fnL
	         with Not_found -> false))) taus;
	  List.iter
	    (fun test -> if !res then raise Found_fn;
               res := test_fn_name test.idl n;
               res := (!res || (test_fn_name test.idr n));
               res := (!res || (test_fn_nameL test.targs n));
               res := (!res || 
                 (try
	           let fnL = Hashtbl.find !(!p.fns) test.tcont in 
	           List.mem n !fnL
                 with Not_found -> false))) tests)) !(!p.comps.(!i)).act_sums)
    with Found_fn -> ignore 0);
    incr i;
  done;
  !res

(***)

(* Auxiliar functions to free_names *)

let free_name n h res =
  match n with
    Fname(s) -> 
      if not (Hashtbl.mem !h s) then
	(Hashtbl.add !h s 0;
	 res := s::!res)
  | _ -> ignore n

let rec free_nameL l h res =
  match l with 
    [] -> ignore l
  | hd::tl -> 
      free_name hd h res;
      free_nameL tl h res

let rec fn_eqs_aux l h res =
  match l with
    [] -> ignore l
  | hd::tl -> 
      (if not (Hashtbl.mem !h hd) then
	(Hashtbl.add !h hd 0;
	 res := hd::!res));
      fn_eqs_aux tl h res

let fn_eqs p c h res =
  try 
    let fnL = Hashtbl.find !(!p.fns) c in
    fn_eqs_aux !fnL h res
  with Not_found -> ignore c

(*** Returns the set of free names of a process ***)

let free_names p =
  let h = ref (Hashtbl.create 100) in
  let res = ref [] in
  for i = 0 to !p.n_comps-1 do
    for j = 0 to !(!p.comps.(i)).nfnouts-1 do
      free_name !(!p.comps.(i)).fn_outs.(j).sub h res;
      free_nameL !(!p.comps.(i)).fn_outs.(j).obj h res;
      free_nameL !(!p.comps.(i)).fn_outs.(j).args h res;
      fn_eqs p !(!p.comps.(i)).fn_outs.(j).cont h res
    done;
    for j = 0 to !(!p.comps.(i)).nfninps-1 do
      free_name !(!p.comps.(i)).fn_inps.(j).sub h res;
      free_nameL !(!p.comps.(i)).fn_inps.(j).args h res;
      fn_eqs p !(!p.comps.(i)).fn_inps.(j).cont h res
    done;
    for j = 0 to !(!p.comps.(i)).nbnouts-1 do
      free_nameL !(!p.comps.(i)).bn_outs.(j).obj h res;
      free_nameL !(!p.comps.(i)).bn_outs.(j).args h res;
      fn_eqs p !(!p.comps.(i)).bn_outs.(j).cont h res
    done;
    for j = 0 to !(!p.comps.(i)).nbninps-1 do
      free_nameL !(!p.comps.(i)).bn_inps.(j).args h res;
      fn_eqs p !(!p.comps.(i)).bn_inps.(j).cont h res
    done;
    for j = 0 to !(!p.comps.(i)).ntests-1 do
      free_name !(!p.comps.(i)).id_tests.(j).idl h res;
      free_name !(!p.comps.(i)).id_tests.(j).idr h res;
      free_nameL !(!p.comps.(i)).id_tests.(j).targs h res;
      fn_eqs p !(!p.comps.(i)).id_tests.(j).tcont h res
    done;
    for j = 0 to !(!p.comps.(i)).ntaus-1 do
      free_nameL !(!p.comps.(i)).act_taus.(j).tau_args h res;
      fn_eqs p !(!p.comps.(i)).act_taus.(j).tau_cont h res
    done;
    List.iter (fun sum -> match sum with (acts,taus,tests) ->
      (List.iter
	(fun act -> 
	  free_name act.sub h res; 
	  (if (act.t = Out_type) then free_nameL act.obj h res);
	  free_nameL act.args h res;
	  fn_eqs p act.cont h res) acts;
      List.iter
        (fun tau ->
	  free_nameL tau.tau_args h res;
	  fn_eqs p tau.tau_cont h res) taus;
      List.iter
        (fun test ->
	  free_name test.idl h res;
	  free_name test.idr h res;
	  free_nameL test.targs h res;
	  fn_eqs p test.tcont h res) tests)) !(!p.comps.(i)).act_sums;
  done;
  !res

(***)

(*** Returns the number of components of a process ***)

let num_comps p = !p.n_comps

(***)

(*** Determines if a process is empty ***)

let empty_proc p =
  ((num_comps p) = 1) &&  
  (!(!p.comps.(0)).nrests = 0) && 
  (!(!p.comps.(0)).nfnouts = 0) &&
  (!(!p.comps.(0)).nfninps = 0) &&
  (!(!p.comps.(0)).nbnouts = 0) &&
  (!(!p.comps.(0)).nbninps = 0) &&
  (!(!p.comps.(0)).ntests = 0) &&
  (!(!p.comps.(0)).ntaus = 0) &&
  (!(!p.comps.(0)).nsums = 0)

(***)

(* Auxiliar function to total_acts *)

let count_acts_comp p pos =
  !(!p.comps.(pos)).nfnouts + !(!p.comps.(pos)).nfninps
    + !(!p.comps.(pos)).nbnouts + !(!p.comps.(pos)).nbninps
    + !(!p.comps.(pos)).ntests + !(!p.comps.(pos)).ntaus + !(!p.comps.(pos)).nsums

(*** Returns the number of actions of a process ***)

let total_acts p =
  let res = ref 0 in
  for i = 0 to !p.n_comps-1 do
    res := !res+(count_acts_comp p i)
  done;
  !res

(***)

(*** Builds two processes by separating an existing one ***)

let extract_comps p is size dim1 dim2 =
  let p1 = {n_comps = dim1; comps = Array.create dim1 (ref (nil_component())); env = !p.env; fns = !p.fns} in
  let p2 = {n_comps = dim2; comps = Array.create dim2 (ref (nil_component())); env = !p.env; fns = !p.fns} in
  let j = ref 0 in
  let k = ref 0 in
  for i = 0 to size-1 do
    if List.mem i is then
      (p1.comps.(!j) <- !p.comps.(i);
       incr j)
    else
      (p2.comps.(!k) <- !p.comps.(i);
       incr k)
  done;
  (ref p1, ref p2)

(***)

(*** Builds a pair of processes by composing with the empty process ***)

let comp_empty p left =
  let empty = {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()} in
  if left then
    (ref empty, p)
  else
    (p, ref empty)

(***)

(*** Returns the number of restrictions of a process component ***)

let nrests_comp p pos = !(!p.comps.(pos)).nrests

(***)

(*** Finds a component that holds restrictions ***)

let find_res p pos = 
  let found = ref false in
  let i = ref pos in
  let size = (num_comps p) in
  while (!i < size) && (not !found) do
    if !(!p.comps.(!i)).nrests > 0 then
      found := true
    else
      incr i
  done;
  !i

(***)

(* Auxiliar functions to handle process updates *)

let instantiate_proc p num_comps comp_num rL fnoL bnoL fniL bniL id_ts act_ts act_ss =
  let size = !p.n_comps + num_comps -1 in
  let res = {n_comps = size; comps = Array.create size (ref (nil_component())); env = !p.env; fns = !p.fns} in
  for i = 0 to size-1 do
    if i < comp_num then
      res.comps.(i) <- !p.comps.(i)
    else if i < !p.n_comps-1 then
      res.comps.(i) <- !p.comps.(i+1)
    else
      res.comps.(i) <- ref (new_component (rL.(i-(!p.n_comps-1))) (fnoL.(i-(!p.n_comps-1))) 
			      (bnoL.(i-(!p.n_comps-1))) (fniL.(i-(!p.n_comps-1))) (bniL.(i-(!p.n_comps-1))) 
			      (id_ts.(i-(!p.n_comps-1))) (act_ts.(i-(!p.n_comps-1))) (act_ss.(i-(!p.n_comps-1))))
  done;
  ref res

let instantiate_proc2 p num_comps comp1 comp2 rL fnoL bnoL fniL bniL id_ts act_ts act_ss =
  let size = !p.n_comps + num_comps - 2 in
  let res = {n_comps = size; comps = Array.create size (ref (nil_component())); env = !p.env; fns = !p.fns} in
  let min_comp = min comp1 comp2 in
  let max_comp = max comp1 comp2 in
  for i = 0 to size-1 do
    if (i < min_comp) then
      res.comps.(i) <- !p.comps.(i)
    else if (i < (max_comp-1)) then
      res.comps.(i) <- !p.comps.(i+1)
    else if (i < (!p.n_comps-2)) then
      res.comps.(i) <- !p.comps.(i+2)
    else
      res.comps.(i) <- ref (new_component (rL.(i-(!p.n_comps-2))) (fnoL.(i-(!p.n_comps-2))) 
			      (bnoL.(i-(!p.n_comps-2))) (fniL.(i-(!p.n_comps-2))) (bniL.(i-(!p.n_comps-2))) 
			      (id_ts.(i-(!p.n_comps-2))) (act_ts.(i-(!p.n_comps-2))) (act_ss.(i-(!p.n_comps-2))))
  done;
  ref res

(* Restricted name update identification *)

let rest_marker comp start_rest pos rmarker =
  let count = ref start_rest in
  for i = 0 to !comp.nrests-1 do
    if i <> pos then
      (Hashtbl.add !rmarker (get_string !comp.rests.(i)) !count;
       incr count)
  done

(* Action update handling *)

let proc_name arg oldn newn marker rmarker pos =
  match arg with
    Bname(s) -> 
      if s = oldn then
	Fname(newn)
      else
	(let k = Hashtbl.find !rmarker s in
	 marker.(pos).(k) <- true;
	 Bname(s))
  | Fname(s) ->
      Fname(s)
  | Iname(i) ->
      Iname(i)

let rec proc_nameL l oldn newn marker rmarker pos =
  match l with
    [] -> []
  | hd::tl -> 
      (proc_name hd oldn newn marker rmarker pos)::
      (proc_nameL tl oldn newn marker rmarker pos)

let proc_act act oldn newn marker rmarker pos fnsub =
  {t = act.t;
   sub = if fnsub then act.sub else proc_name act.sub oldn newn marker rmarker pos;
   obj = if act.t = Out_type then proc_nameL act.obj oldn newn marker rmarker pos else act.obj;
   cont = act.cont;
   args = proc_nameL act.args oldn newn marker rmarker pos}

let proc_test test oldn newn marker rmarker pos =
  {tst = test.tst;
   idl = proc_name test.idl oldn newn marker rmarker pos;
   idr = proc_name test.idr oldn newn marker rmarker pos;
   tcont = test.tcont;
   targs = proc_nameL test.targs oldn newn marker rmarker pos}

let proc_tau tau oldn newn marker rmarker pos =
  {tau_cont = tau.tau_cont;
   tau_args = proc_nameL tau.tau_args oldn newn marker rmarker pos}

let proc_acts comp marker oldn revn start_act rmarker start_outs start_inps start_tests start_taus start_sums inp_ind out_ind fn ti taui =
  let outs = ref start_outs in
  let accum = ref start_act in
  for i = 0 to !comp.nfnouts-1 do
    if ((not fn) || (out_ind <> i)) then
      outs := ((proc_act !comp.fn_outs.(i) oldn revn marker rmarker (!accum+i) true),(!accum+i))::!outs
    else
      decr accum
  done;
  accum := !accum + !comp.nfnouts;
  for i = 0 to !comp.nbnouts-1 do
    if (fn || (out_ind <> i)) then
      outs := ((proc_act !comp.bn_outs.(i) oldn revn marker rmarker (!accum+i) false),(!accum+i))::!outs
    else
      decr accum
  done;
  accum := !accum + !comp.nbnouts;
  let inps = ref start_inps in
  for i = 0 to !comp.nfninps-1 do
    if ((not fn) || (inp_ind <> i)) then
      inps := ((proc_act !comp.fn_inps.(i) oldn revn marker rmarker (!accum+i) true),(!accum+i))::!inps
    else
      decr accum
  done;
  accum := !accum + !comp.nfninps;
  for i = 0 to !comp.nbninps-1 do
    if (fn || (inp_ind <> i)) then
      inps := ((proc_act !comp.bn_inps.(i) oldn revn marker rmarker (!accum+i) false),(!accum+i))::!inps
    else
      decr accum
  done;
  accum := !accum + !comp.nbninps;
  let tests = ref start_tests in
  for i = 0 to !comp.ntests-1 do
    if (i <> ti) then
      tests := ((proc_test !comp.id_tests.(i) oldn revn marker rmarker (!accum+i)),(!accum+i))::!tests
    else
      decr accum
  done;
  accum := !accum + !comp.ntests;
  let taus = ref start_taus in
  for i = 0 to !comp.ntaus-1 do
    if (i <> taui) then
      taus := ((proc_tau !comp.act_taus.(i) oldn revn marker rmarker (!accum+i)),(!accum+i))::!taus
    else
      decr accum
  done;
  accum := !accum + !comp.ntaus;
  let sums = ref start_sums in
  let inp_sum_i = ref 
      (if fn then
	!comp.nfninps
      else
	!comp.nbninps) in
  let out_sum_i = ref
      (if fn then
	!comp.nfnouts
      else
	!comp.nbnouts) in
  let test_sum_i = ref !comp.ntests in
  let tau_sum_i = ref !comp.ntaus in
  List.iter (fun l -> match l with (acts,taus,tests) ->
    (if (((inp_ind >= !inp_sum_i) && (inp_ind < (!inp_sum_i+(List.length acts))))
      || ((out_ind >= !out_sum_i) && (out_ind < (!out_sum_i+(List.length acts))))
      || ((taui >= !tau_sum_i) && (taui < (!tau_sum_i+(List.length taus))))
      || ((ti >= !test_sum_i) && (ti < (!test_sum_i+(List.length tests))))) then
      (inp_sum_i := !inp_sum_i+(List.length acts);
       out_sum_i := !out_sum_i+(List.length acts);
       tau_sum_i := !tau_sum_i+(List.length taus);
       test_sum_i := !test_sum_i+(List.length tests))
    else
      (inp_sum_i := !inp_sum_i+(List.length acts);
       out_sum_i := !out_sum_i+(List.length acts);
       tau_sum_i := !tau_sum_i+(List.length taus);
       test_sum_i := !test_sum_i+(List.length tests);
       let new_acts = ref [] in
       List.iter 
	 (fun act -> 
	   new_acts := (proc_act act oldn revn marker rmarker !accum false)::!new_acts) acts;
       let new_taus = ref [] in
       List.iter
	 (fun tau ->
	   new_taus := (proc_tau tau oldn revn marker rmarker !accum)::!new_taus) taus;
       let new_tests = ref [] in
       List.iter
	 (fun test ->
	   new_tests := (proc_test test oldn revn marker rmarker !accum)::!new_tests) tests;
       sums := ((!new_acts,!new_taus,!new_tests),!accum)::!sums; incr accum))) !comp.act_sums;
  (outs,inps,tests,taus,sums) 
    
(* Restring name update handling *)

let proc_rests comp_names num_comps comp pos res_names start_pos =
  for i = 0 to !comp.nrests-1 do
    let new_rest_pos = 
      if i < pos then i
      else if i < !comp.nrests-1 then (i+1)
      else (-1)
    in
    if (new_rest_pos <> -1) && (comp_names.(i+start_pos) <> 0) then
      res_names.(comp_names.(i+start_pos)-1) <- 
	Bname(get_string !comp.rests.(new_rest_pos))
	::(res_names.(comp_names.(i+start_pos)-1))
  done

(***)

(*** Returns a process where a restricted name revelation has taken place ***)

let rev_comps p comp_num rest_num revn =
  let comp = !p.comps.(comp_num) in
  let oldn = get_string !comp.rests.(rest_num) in
  let marker = Array.make_matrix (count_acts_comp p comp_num) (!comp.nrests-1) false in 
  let rmarker = ref (Hashtbl.create (!comp.nrests)) in 
  rest_marker comp 0 rest_num rmarker;
  let (outs,inps,tests,taus,sums) = proc_acts comp marker oldn revn 0 rmarker [] [] [] [] [] (-1) (-1) true (-1) (-1) in
  let (num_comps, comp_acts, comp_names) = comps marker in
  let (fnoL,bnoL,fniL,bniL,id_ts,act_ts, act_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
  let rL = Array.create num_comps ([]) in
  proc_rests comp_names num_comps comp rest_num rL 0;
  instantiate_proc p num_comps comp_num rL fnoL bnoL fniL bniL id_ts act_ts act_ss

(***)

(* Auxiliar functions to find_label *)

let match_name s n =
  match n with
    Bname(x) -> false
  | Fname(x) -> x = s
  | Iname(i) -> false

let rec match_list sl nl marker i h =
  match nl with
    [] -> 
      (match sl with 
	[] -> (true,[])
      | s::sltl -> (false,[]))
  | Bname(n)::nltl ->
      if marker.(i) then
	(match sl with
	  [] -> (false,[])
	| s::sltl -> 
	    let (res,resL) = match_list sltl nltl marker (i+1) h in
	    if res then
			(if not (Hashtbl.mem !h n) then
				(let ns = (if s = "_" then fresh_name() else s) in
				Hashtbl.add !h n ns;
				(true,(ns,n)::resL))
	        else
				(if (Hashtbl.find !h n) = s then
					(true,resL)
				else
					(false,[])))
		else
			(false,[]))
      else
	(false,[])
  | Fname(n)::nltl ->
      (match sl with
	[] -> (false,[])
      | s::sltl -> 
	  let (res,resL) = match_list sltl nltl marker (i+1) h in
	  if res then
	    ((s = n) || (s = "_"), resL)
	  else
	    (false,[]))
  | Iname(i)::nltl ->
      (false,[])

let match_lab t sub obj act marker =
  if t <> act.t then
    (false,[])
  else
    (if t = Inp_type then
      (((match_name sub act.sub) && ((List.length obj) = (List.length act.obj))),[])
    else
      (if ((match_name sub act.sub) && ((List.length obj) = (List.length act.obj))) then
         (match_list obj act.obj marker 0 (ref (Hashtbl.create (List.length obj))))
      else
         (false,[])))

(***)

(*** Finds an action given the label and a starting point ***)

let find_label p lab comp ind marker =
  let not_found = ref true in
  let reveals = ref [] in
  let size1 = !p.n_comps in
  let cur_comp = ref comp in
  let cur_ind = ref ind in
  (match lab with (t,sub,obj) ->
    (while (!cur_comp < size1) && !not_found  do
      let (size2,acts) =
	if t = Inp_type then 
	  (!(!p.comps.(!cur_comp)).nfninps,ref (!(!p.comps.(!cur_comp)).fn_inps))
	else
	  (!(!p.comps.(!cur_comp)).nfnouts,ref (!(!p.comps.(!cur_comp)).fn_outs))
      in
      while (!cur_ind < size2) && !not_found do
	let (res,resL) = match_lab t sub obj !acts.(!cur_ind) marker in
	if res then
	  (not_found := false;
	   reveals := resL)
	else
	  incr cur_ind
      done;
      (if (!not_found) then
	let sum_ind = ref (!cur_ind-size2) in
	try
	  (List.iter (fun sum -> match sum with (acts,taus,tests) ->
	    (List.iter
	       (fun act -> 
		 if !sum_ind = 0 then
		   (let (res,resL) = match_lab t sub obj act marker in
		   if res then
		     (not_found := false;
		      reveals := resL;
		      raise Found)
		   else
		     incr cur_ind)
		 else
		   decr sum_ind) acts)) !(!p.comps.(!cur_comp)).act_sums)
	with Found -> ignore 1);
      if !not_found then
	(incr cur_comp;
	 cur_ind := 0)
    done));
  (!not_found,!cur_comp,!cur_ind,!reveals)

(***)

(*** Finds a restricted name component ***)

let find_rest p comp n =
  let res = ref (-1) in
  let i = ref 0 in
  while (!res = -1) && (!i < !(!p.comps.(comp)).nrests) do
    if get_string (!(!p.comps.(comp)).rests.(!i)) = n then
      res := !i
    else
      incr i
  done;
  !res

(***)

(*** Finds a component that holds restrictions ***)

let find_rests p =
  let res = ref (-1) in
  let i = ref 0 in
  while (!res = -1) && (!i < !p.n_comps) do
    if (!(!p.comps.(!i)).nrests > 0) then
      res := !i
    else
      incr i
  done;
  !res

(***)

(* Auxiliar functions to react_label *)

let cut_comp p pos = 
  let res = 
    {n_comps = !p.n_comps-1; 
     comps = Array.create (!p.n_comps-1) (ref (nil_component())); 
     env = !p.env; fns = !p.fns} 
  in
  for i = 0 to !p.n_comps -2 do
    if i < pos then
      res.comps.(i) <- !p.comps.(i)
    else
      res.comps.(i) <- !p.comps.(i+1)
  done;
  ref res

let cut_two_comps p pos1 pos2 =
  let res = 
    {n_comps = !p.n_comps-2;
     comps = Array.create (!p.n_comps-2) (ref (nil_component()));
     env = !p.env; fns = !p.fns}
  in
  let min_pos = min pos1 pos2 in
  let max_pos = max pos1 pos2 in
  for i = 0 to !p.n_comps-3 do
    if i < min_pos then
      res.comps.(i) <- !p.comps.(i)
    else if (i < (max_pos-1)) then
      res.comps.(i) <- !p.comps.(i+1)
    else 
      res.comps.(i) <- !p.comps.(i+2)
  done;
  ref res

let rec react_label_args inpL sub_args =
  let aux = Array.of_list inpL in
  for i = 0 to (Array.length sub_args)-1 do
    match sub_args.(i) with 
      Iname(k) -> sub_args.(i) <- Fname(aux.(k))
    | _ -> ignore i
  done
    
(* Handles the process update after the transition *)

let react_label_aux p pos eq act args ind inp =
  let comp = !p.comps.(pos) in
  let marker = Array.make_matrix 
      ((count_acts eq)+(count_acts_comp p pos) -1)
      ((count_rests eq) + (!comp.nrests)) false
  in
  let sub_args = Array.of_list act.args in
  react_label_args args sub_args;
  let sub_rests = fresh_rests (count_rests eq) in
  let rmarker = ref (Hashtbl.create (!comp.nrests)) in 
  rest_marker comp (count_rests eq) (!comp.nrests) rmarker;
  let (os,is,tsts,ts,ss) = eq_acts eq marker sub_args sub_rests 0 rmarker [] [] [] [] [] in
  let freshn = fresh_name() in
  let (inp_ind,out_ind) = if inp then (ind,-1) else (-1,ind) in
  let (outs,inps,tests,taus,sums) = 
    proc_acts comp marker freshn freshn (count_acts eq) rmarker !os !is !tsts !ts !ss inp_ind out_ind true (-1) (-1) in
  let (num_comps, comp_acts, comp_names) = comps marker in
  let (fnoL, bnoL, fniL, bniL,id_ts,act_ts,act_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
  let rL = Array.create num_comps ([]) in
  eq_rests comp_names num_comps sub_rests (count_rests eq) rL 0;
  proc_rests comp_names num_comps comp (!comp.nrests) rL (count_rests eq);
  instantiate_proc p num_comps pos rL fnoL bnoL fniL bniL id_ts act_ts act_ss

(***)

let rec get_pos_sum sum ind i =
  match sum with 
    [] -> raise Error
  | hd::tl -> 
      if ind = i then
	hd
      else
	get_pos_sum tl ind (i+1)

let rec get_act_sums sums ind i =
  match sums with
    [] -> raise Error
  | (acts,taus,tests)::tl ->
      if ind < ((List.length acts)+i) then
	get_pos_sum acts ind i
      else
	get_act_sums tl ind (i+(List.length acts))

(***)

(*** Returns a process where a transition on a given label has taken place ***)

let react_label lab pos ind p =
  match lab with (t,sub,obj) ->
    let (act,inp) = 
      if t = Inp_type then
	(if ind < !(!p.comps.(pos)).nfninps then
	  (!(!p.comps.(pos)).fn_inps.(ind),true)
	else
	  (get_act_sums !(!p.comps.(pos)).act_sums (ind - !(!p.comps.(pos)).nfninps) 0, true))
      else
	(if ind < !(!p.comps.(pos)).nfnouts then
	  (!(!p.comps.(pos)).fn_outs.(ind),false)
	else
	  (get_act_sums !(!p.comps.(pos)).act_sums (ind- !(!p.comps.(pos)).nfnouts) 0, false))
    in
    if is_void_eqvar act.cont then
      (if !p.n_comps = 1 then
	ref {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()}
      else
	cut_comp p pos)
    else
      (let eq = Hashtbl.find !(!p.env) act.cont in
      react_label_aux p pos eq act obj ind inp)

(***)

(* Auxiliar functions to find_fn_tau and find_bn_tau *)

let match_tau_name n1 n2 =
  match n1 with
    Bname(x) -> 
      (match n2 with 
	Bname(y) -> x=y
      | Fname(y) -> false
      | Iname(i) -> false)
  | Fname(x) ->
      (match n2 with
	Bname(y) -> false
      | Fname(y) -> x=y
      | Iname(i) -> false)
  | Iname(i) -> false

let match_tau inp out =
  (inp.t = Inp_type) && (out.t = Out_type) &&
  (match_tau_name inp.sub out.sub) && ((List.length inp.obj) = (List.length out.obj))

let is_fn_act act =
  match act.sub with
    Fname(s) -> true
  | _ -> false

(***)

(*** Finds a synchronization in a free name ***)

let find_fn_tau p inpc inpi outc outi =
  let not_found = ref true in
  let inp_comp = ref inpc in
  let inp_ind = ref inpi in
  let out_comp = ref outc in
  let out_ind = ref outi in
  while (!inp_comp < !p.n_comps) && !not_found do
    while (!inp_ind < !(!p.comps.(!inp_comp)).nfninps) && !not_found do
      (while (!out_comp < !p.n_comps) && !not_found do
	while (!out_ind < !(!p.comps.(!out_comp)).nfnouts) && !not_found do
	  if match_tau !(!p.comps.(!inp_comp)).fn_inps.(!inp_ind) 
	      !(!p.comps.(!out_comp)).fn_outs.(!out_ind) then
	    not_found := false
	  else
	    incr out_ind
	done;
	(if !not_found then
	  let out_sum_ind = ref (!out_ind - !(!p.comps.(!out_comp)).nfnouts) in
	  try
	    (List.iter (fun sum -> (match sum with (acts,taus,tests) -> List.iter
		(fun out -> 
		  if !out_sum_ind = 0 then
		    ((if (is_fn_act out) && (out.t = Out_type) then
		      if match_tau !(!p.comps.(!inp_comp)).fn_inps.(!inp_ind) out then
			(not_found := false;
			 raise Found));
		     incr out_ind)
		  else
		    decr out_sum_ind) acts)) !(!p.comps.(!out_comp)).act_sums)
	  with Found -> ignore 1);
	if !not_found then
	  (incr out_comp;
	   out_ind := 0)
      done);
      if !not_found then
	(incr inp_ind;
	 out_comp := 0;
	 out_ind := 0)
    done;
    (if (!not_found) then
      let inp_sum_ind = ref (!inp_ind - !(!p.comps.(!inp_comp)).nfninps) in
      let inp_sum_pos = ref 0 in
      try
	(List.iter (fun inp_sum -> (match inp_sum with (acts,taus,tests) -> List.iter
	    (fun inp -> 
	      if !inp_sum_ind = 0 then
		(if (is_fn_act inp) && (inp.t = Inp_type) then
		  while (!out_comp < !p.n_comps) && !not_found do
		    while (!out_ind < !(!p.comps.(!out_comp)).nfnouts) && !not_found do
		      if match_tau inp !(!p.comps.(!out_comp)).fn_outs.(!out_ind) then
			(not_found := false;
			 raise Found)
		      else
			incr out_ind
		    done;
		    (if !not_found then
		      let out_sum_ind = ref (!out_ind - !(!p.comps.(!out_comp)).nfnouts) in
		      let out_sum_pos = ref 0 in
		      List.iter (fun out_sum -> (match out_sum with (acts,taus,tests) ->
			(if (!inp_comp <> !out_comp) || (!inp_sum_pos <> !out_sum_pos) then 
			  List.iter
			    (fun out -> 
			      if !out_sum_ind = 0 then
				((if (is_fn_act out) && (out.t = Out_type) then
				  if match_tau inp out then
				    (not_found := false;
				     raise Found));
				 incr out_ind)
			      else
				decr out_sum_ind) acts
			else 
			  (let out_sum_len = (List.length acts) in
			  if (!out_sum_ind >= out_sum_len) then
			    out_sum_ind := !out_sum_ind - out_sum_len
			  else
		            (out_sum_ind := 0;
			     out_ind := !out_ind + out_sum_len))));
			incr out_sum_pos) !(!p.comps.(!out_comp)).act_sums);
		    if !not_found then
		      (incr out_comp;
		       out_ind := 0)
		  done;
		 incr inp_ind;
		 out_comp := 0;
		 out_ind := 0)
	      else
		decr inp_sum_ind) acts; incr inp_sum_pos)) !(!p.comps.(!inp_comp)).act_sums)
      with Found -> ignore 1);
    if !not_found then
      (incr inp_comp;
       inp_ind := 0;
       out_comp := 0;
       out_ind := 0)
  done;
  (!not_found,!inp_comp,!inp_ind,!out_comp,!out_ind)

(***)

(*** Finds a synchronization in a bound name ***)

let find_bn_tau p c inpi outi =
  let not_found = ref true in
  let comp = ref c in
  let inp_ind = ref inpi in
  let out_ind = ref outi in
  while (!comp < !p.n_comps) && !not_found do
    while (!inp_ind < !(!p.comps.(!comp)).nbninps) && !not_found do
      while (!out_ind < !(!p.comps.(!comp)).nbnouts) && !not_found do
	if match_tau !(!p.comps.(!comp)).bn_inps.(!inp_ind) 
	    !(!p.comps.(!comp)).bn_outs.(!out_ind) then
	  not_found := false
	else
	  incr out_ind
      done;
      (if !not_found then
	let out_sum_ind = ref (!out_ind - !(!p.comps.(!comp)).nbnouts) in
	try
	  (List.iter (fun sum -> (match sum with (acts,taus,tests) -> List.iter
	      (fun out -> 
		if !out_sum_ind = 0 then
		  (if (not (is_fn_act out)) && (out.t = Out_type) then
		    if match_tau !(!p.comps.(!comp)).bn_inps.(!inp_ind) out then
		      (not_found := false;
		       raise Found);
		   incr out_ind)
		else
		  decr out_sum_ind) acts)) !(!p.comps.(!comp)).act_sums)
	with Found -> ignore 1);
      if !not_found then
	(incr inp_ind;
	 out_ind := 0)
    done;
    (if (!not_found) then
      let inp_sum_ind = ref (!inp_ind - !(!p.comps.(!comp)).nbninps) in
      let inp_sum_pos = ref 0 in
      try
	(List.iter (fun inp_sum -> (match inp_sum with (acts,taus,tests) -> List.iter
	    (fun inp -> 
	      if !inp_sum_ind = 0 then
		(if (not (is_fn_act inp)) && (inp.t = Inp_type) then
		  while (!out_ind < !(!p.comps.(!comp)).nbnouts) && !not_found do
		    if match_tau inp !(!p.comps.(!comp)).bn_outs.(!out_ind) then
		      (not_found := false;
		       raise Found)
		    else
		      incr out_ind
		  done;
		 (if (not (is_fn_act inp)) && (inp.t = Inp_type) && !not_found then
		   let out_sum_ind = ref (!out_ind - !(!p.comps.(!comp)).nbnouts) in
		   let out_sum_pos = ref 0 in
		   List.iter (fun out_sum -> (match out_sum with (acts,taus,tests) ->
		     (if !inp_sum_pos <> !out_sum_pos then 
		       List.iter 
			 (fun out -> 
			   if !out_sum_ind = 0 then
			     ((if (not (is_fn_act out)) && (out.t = Out_type) then
			       if match_tau inp out then
				 (not_found := false;
				  raise Found));
			      incr out_ind)
			   else
			     decr out_sum_ind) acts
		     else
		       (let out_sum_len = (List.length acts) in
			if (!out_sum_ind >= out_sum_len) then
			  out_sum_ind := !out_sum_ind - out_sum_len
			else
		          (out_sum_ind := 0;
			   out_ind := !out_ind + out_sum_len)))); 
		     incr out_sum_pos) !(!p.comps.(!comp)).act_sums);
		 incr inp_ind;
		 out_ind := 0)
	      else
		decr inp_sum_ind) acts; incr inp_sum_pos)) !(!p.comps.(!comp)).act_sums)
      with Found -> ignore 1);
    if !not_found then
      (incr comp;
       inp_ind := 0;
       out_ind := 0)
  done;
  (!not_found,!comp,!inp_ind,!out_ind)

(***)

(* Auxiliar function to react_tau_aux *)

let rec react_tau_args inpL sub_args =
  let aux = Array.of_list inpL in
  for i = 0 to (Array.length sub_args)-1 do
    match sub_args.(i) with 
      Iname(k) -> sub_args.(i) <- aux.(k)
    | _ -> ignore i
  done

(* Handles the process update after the synchronization *)

let react_tau_aux p inp_c out_c inp_eq out_eq inp_act out_act inp_i out_i fn =
  let inp_comp = !p.comps.(inp_c) in
  let out_comp = !p.comps.(out_c) in
  let (num_acts,num_rests) = 
    if inp_c <> out_c then
      (((count_acts inp_eq)+(count_acts out_eq)+(count_acts_comp p inp_c)+(count_acts_comp p out_c)-2),
       ((count_rests inp_eq) + (count_rests out_eq) + (!inp_comp.nrests) + (!out_comp.nrests)))
    else
      (((count_acts inp_eq)+(count_acts out_eq)+(count_acts_comp p inp_c) -2),
       ((count_rests inp_eq) + (count_rests out_eq)+ (!inp_comp.nrests)))
  in
  let marker = Array.make_matrix num_acts num_rests false in
  let inp_sub_args = Array.of_list inp_act.args in
  react_tau_args out_act.obj inp_sub_args;
  let out_sub_args = Array.of_list out_act.args in
  let inp_sub_rests = fresh_rests (count_rests inp_eq) in
  let out_sub_rests = fresh_rests (count_rests out_eq) in
  let rmarker = ref (Hashtbl.create (!inp_comp.nrests + !out_comp.nrests)) in
  rest_marker inp_comp ((count_rests inp_eq)+(count_rests out_eq)) (!inp_comp.nrests) rmarker;
  (if inp_c <> out_c then
    rest_marker out_comp ((count_rests inp_eq)+(count_rests out_eq)+(!inp_comp.nrests)) (!out_comp.nrests) rmarker);
  let (os1,is1,tsts1,ts1,ss1) = eq_acts inp_eq marker inp_sub_args inp_sub_rests 0 rmarker [] [] [] [] [] in
  (if (count_rests out_eq) > 0 then
    let i = ref ((count_rests inp_eq)-1) in
    while !i >= 0 do 
      for j = 0 to (count_acts inp_eq)-1 do
	marker.(j).(!i+(count_rests out_eq)) <- marker.(j).(!i);
      done;    
      decr i
    done);
  let (os2,is2,tsts2,ts2,ss2) = 
    eq_acts out_eq marker out_sub_args out_sub_rests (count_acts inp_eq) rmarker !os1 !is1 !tsts1 !ts1 !ss1 in
  let freshn = fresh_name() in
  let start_act = ((count_acts inp_eq)+(count_acts out_eq)) in
  let (outs,inps,tests,taus,sums) =
    if inp_c <> out_c then
      (let (os3,is3,tsts3,ts3,ss3) = 
	proc_acts inp_comp marker freshn freshn start_act rmarker !os2 !is2 !tsts2 !ts2 !ss2 inp_i (-1) fn (-1) (-1) in
      proc_acts out_comp marker freshn freshn (start_act+(count_acts_comp p inp_c)-1) rmarker
	!os3 !is3 !tsts3 !ts3 !ss3 (-1) out_i fn (-1) (-1))
    else      
      proc_acts inp_comp marker freshn freshn start_act rmarker	!os2 !is2 !tsts2 !ts2 !ss2 inp_i out_i fn (-1) (-1)
  in
  let (num_comps, comp_acts,comp_names) = comps marker in
  let (fnoL, bnoL, fniL, bniL, id_ts, act_ts, act_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
  let rL = Array.create num_comps ([]) in
  eq_rests comp_names num_comps out_sub_rests (count_rests out_eq) rL 0;
  eq_rests comp_names num_comps inp_sub_rests (count_rests inp_eq) rL (count_rests out_eq);
  let start_rests = ((count_rests out_eq)+(count_rests inp_eq)) in
  proc_rests comp_names num_comps inp_comp (!inp_comp.nrests) rL start_rests;
  if inp_c <> out_c then
    (proc_rests comp_names num_comps out_comp (!out_comp.nrests) rL (start_rests+(!inp_comp.nrests));
     instantiate_proc2 p num_comps inp_c out_c rL fnoL bnoL fniL bniL id_ts act_ts act_ss)
  else
    instantiate_proc p num_comps inp_c rL fnoL bnoL fniL bniL id_ts act_ts act_ss

(***)

(*** Returns a process where an internal transition has taken place ***)

let react_tau inp_c inp_i out_c out_i fn p =
  let (inp_act,out_act) = 
    if fn then
      ((if inp_i < !(!p.comps.(inp_c)).nfninps then
	!(!p.comps.(inp_c)).fn_inps.(inp_i)
      else
	get_act_sums !(!p.comps.(inp_c)).act_sums (inp_i- !(!p.comps.(inp_c)).nfninps) 0),
       (if out_i < !(!p.comps.(out_c)).nfnouts then
	 !(!p.comps.(out_c)).fn_outs.(out_i)
       else
	 get_act_sums !(!p.comps.(out_c)).act_sums (out_i- !(!p.comps.(out_c)).nfnouts) 0))
    else
      ((if inp_i < !(!p.comps.(inp_c)).nbninps then
	!(!p.comps.(inp_c)).bn_inps.(inp_i)
      else
	get_act_sums !(!p.comps.(inp_c)).act_sums (inp_i- !(!p.comps.(inp_c)).nbninps) 0), 
       (if out_i < !(!p.comps.(out_c)).nbnouts then
	 !(!p.comps.(out_c)).bn_outs.(out_i)
       else
	 get_act_sums !(!p.comps.(out_c)).act_sums (out_i- !(!p.comps.(out_c)).nbnouts) 0))
  in
  let inp_eq = 
    if is_void_eqvar inp_act.cont then
      nil_eq()
    else
      Hashtbl.find !(!p.env) inp_act.cont 
  in
  let out_eq = 
    if is_void_eqvar out_act.cont then
      nil_eq()
    else
      Hashtbl.find !(!p.env) out_act.cont 
  in
  let void_conts = 
    (count_rests inp_eq = 0) && (count_acts inp_eq = 0) &&
    (count_rests out_eq = 0) && (count_acts out_eq = 0)
  in
  if (void_conts &&
      (((!p.n_comps = 1) && ((count_acts_comp p 0) = 2)) ||
      ((!p.n_comps = 2) && ((count_acts_comp p inp_c) = 1) && ((count_acts_comp p out_c) = 1))))
  then
    ref {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()}
  else if (void_conts && (inp_c = out_c) && ((count_acts_comp p inp_c) = 2)) then
    cut_comp p inp_c
  else if (void_conts && ((count_acts_comp p inp_c) = 1) && ((count_acts_comp p out_c) = 1)) then
    cut_two_comps p inp_c out_c
  else
    react_tau_aux p inp_c out_c inp_eq out_eq inp_act out_act inp_i out_i fn

(***)

(*** Returns the different number of arguments of communications in a given name ***)

let get_num_args p n =
  let h = Hashtbl.create 100 in
  let res = ref [] in
  for i = 0 to !p.n_comps-1 do
    for j = 0 to !(!p.comps.(i)).nfninps-1 do
      let len = (List.length !(!p.comps.(i)).fn_inps.(j).obj) in
      if ((get_string !(!p.comps.(i)).fn_inps.(j).sub) = n) &&
	(not (Hashtbl.mem h len)) then
	(res := len::!res;
	 Hashtbl.add h len true)
    done;
    List.iter (fun sum -> (match sum with (acts,taus,tests) -> List.iter
	(fun inp -> let len = (List.length inp.obj) in
	if ((inp.t = Inp_type) && (is_fn_act inp) && (get_string inp.sub)=n) && (not (Hashtbl.mem h len)) then 
	  (res := len::!res;
	   Hashtbl.add h len true)) acts)) !(!p.comps.(i)).act_sums
  done;
  !res

(***)

(* Auxiliar function to find_test *)

let match_id test =
  match test.idl with
    Fname(s1) -> 
      (match test.idr with
	Fname(s2) -> if (test.tst = Equations.Equals_type) then s1 = s2
                     else not (s1 = s2)
      | _ -> false)
  | Bname(s1) ->
      (match test.idr with
	Bname(s2) -> if (test.tst = Equations.Equals_type) then s1 = s2
                     else not (s1 = s2)
      | _ -> false)
  | Iname(s1) -> false

(*** Finds a test prefix ready to fire ***)

let find_test p comp ind =
  let s1 = !p.n_comps in
  let found = ref false in
  let tes_comp = ref comp in
  let tes_ind = ref ind in
  while (!tes_comp < s1) && (not !found) do
    while (!tes_ind < !(!p.comps.(!tes_comp)).ntests) && (not !found) do
      if match_id !(!p.comps.(!tes_comp)).id_tests.(!tes_ind) then
	found := true
      else
	incr tes_ind
    done;
    (if not !found then
      (let sum_ind = ref (!tes_ind - !(!p.comps.(!tes_comp)).ntests) in
      try
        (List.iter (fun sum -> match sum with (acts,taus,tests) ->
	   (List.iter
	     (fun test -> 
	        if !sum_ind = 0 then
		  if match_id test then
		    (found := true;
	  	    raise Found)
		  else
		    (incr tes_ind)
	        else
		  decr sum_ind) tests)) !(!p.comps.(!tes_comp)).act_sums)
	  with Found -> ignore 1));
    if not !found then
      (incr tes_comp;
       tes_ind := 0)
  done;
  (!found,!tes_comp,!tes_ind)

(***)

(* Handles the process update after the ttest firing transition *)

let react_test_aux p pos ind eq test =
  let comp = !p.comps.(pos) in
  let marker = Array.make_matrix 
      ((count_acts eq)+(count_acts_comp p pos) -1)
      ((count_rests eq) + (!comp.nrests)) false
  in
  let sub_args = Array.of_list test.targs in
  let sub_rests = fresh_rests (count_rests eq) in
  let rmarker = ref (Hashtbl.create (!comp.nrests)) in 
  rest_marker comp (count_rests eq) (!comp.nrests) rmarker;
  let (os,is,tsts,ts,ss) = eq_acts eq marker sub_args sub_rests 0 rmarker [] [] [] [] [] in
  let freshn = fresh_name() in
  let (outs,inps,tests,taus,sums) = 
    proc_acts comp marker freshn freshn (count_acts eq) rmarker !os !is !tsts !ts !ss (-1) (-1) true ind (-1) in
  let (num_comps, comp_acts, comp_names) = comps marker in
  let (fnoL, bnoL, fniL, bniL,id_ts,act_ts,inp_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
  let rL = Array.create num_comps ([]) in
  eq_rests comp_names num_comps sub_rests (count_rests eq) rL 0;
  proc_rests comp_names num_comps comp (!comp.nrests) rL (count_rests eq);
  instantiate_proc p num_comps pos rL fnoL bnoL fniL bniL id_ts act_ts inp_ss

(***)

(* Auxiliar function to react_test *)

let rec get_test_sums sums ind i =
  match sums with
    [] -> raise Error
  | (acts,taus,tests)::tl ->
      if ind < ((List.length tests)+i) then
	get_pos_sum tests ind i
      else
	get_test_sums tl ind (i+(List.length tests))

(*** Returns a process where a test firing transition has taken place ***)

let react_test pos ind p =
  let test = 
    (if ind < !(!p.comps.(pos)).ntests then
      !(!p.comps.(pos)).id_tests.(ind)
    else
      get_test_sums !(!p.comps.(pos)).act_sums (ind - !(!p.comps.(pos)).ntests) 0
    )
  in
  if (is_void_eqvar test.tcont) && (!p.n_comps = 1) && ((count_acts_comp p pos) = 1) then
    ref {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()}
  else if (is_void_eqvar test.tcont) && ((count_acts_comp p pos) = 1) then
    cut_comp p pos
  else
    (let test_eq = 
      if is_void_eqvar test.tcont then
	nil_eq()
      else
	Hashtbl.find !(!p.env) test.tcont 
    in
    react_test_aux p pos ind test_eq test)

(***)

(*** Finds a tau prefix ***)

let find_tau_pref p comp ind =
  let s1 = !p.n_comps in
  let found = ref false in
  let tau_comp = ref comp in
  let tau_ind = ref ind in
  while (!tau_comp < s1) && (not !found) do
    (if (!tau_ind < !(!p.comps.(!tau_comp)).ntaus) && (not !found) then
      found := true);
    (if not !found then 
      (let sum_ind = ref (!tau_ind - !(!p.comps.(!tau_comp)).ntaus) in 
      try
        (List.iter (fun sum -> match sum with (acts,taus,tests) ->
	   (List.iter
	     (fun tau -> 
	        if !sum_ind = 0 then
		    (found := true;
		    raise Found)
	        else
	  	  decr sum_ind) taus)) !(!p.comps.(!tau_comp)).act_sums)
  	  with Found -> ignore 1));
    if not !found then
      (incr tau_comp;
       tau_ind := 0)
  done;
  (!found,!tau_comp,!tau_ind)

(***)

(* Auxiliar function to react_tau_pref *)

let rec get_tau_sums sums ind i =
  match sums with
    [] -> raise Error
  | (acts,taus,tests)::tl ->
      if ind < ((List.length taus)+i) then
	get_pos_sum taus ind i
      else
	get_tau_sums tl ind (i+(List.length taus))

(***)

(* Handles the process update after the a tau prefix firing *)

let react_tau_pref_aux p pos ind eq tau =
  let comp = !p.comps.(pos) in
  let marker = Array.make_matrix 
      ((count_acts eq)+(count_acts_comp p pos) -1)
      ((count_rests eq) + (!comp.nrests)) false
  in
  let sub_args = Array.of_list tau.tau_args in
  let sub_rests = fresh_rests (count_rests eq) in
  let rmarker = ref (Hashtbl.create (!comp.nrests)) in 
  rest_marker comp (count_rests eq) (!comp.nrests) rmarker;
  let (os,is,tsts,ts,ss) = eq_acts eq marker sub_args sub_rests 0 rmarker [] [] [] [] [] in
  let freshn = fresh_name() in
  let (outs,inps,tests,taus,sums) = 
    proc_acts comp marker freshn freshn (count_acts eq) rmarker !os !is !tsts !ts !ss (-1) (-1) true (-1) ind in
  let (num_comps, comp_acts, comp_names) = comps marker in
  let (fnoL, bnoL, fniL, bniL,id_ts,act_ts,inp_ss) = create_comps outs inps tests taus sums num_comps comp_acts in
  let rL = Array.create num_comps ([]) in
  eq_rests comp_names num_comps sub_rests (count_rests eq) rL 0;
  proc_rests comp_names num_comps comp (!comp.nrests) rL (count_rests eq);
  instantiate_proc p num_comps pos rL fnoL bnoL fniL bniL id_ts act_ts inp_ss

(***)

(*** Returns a process where a tau prefix firing transition has taken place ***)

let react_tau_pref pos ind p =
  let tau =
  (if ind < !(!p.comps.(pos)).ntaus then
    !(!p.comps.(pos)).act_taus.(ind)
  else
    get_tau_sums !(!p.comps.(pos)).act_sums (ind - !(!p.comps.(pos)).ntaus) 0
  )
  in
  if (is_void_eqvar tau.tau_cont) && (!p.n_comps = 1) && ((count_acts_comp p pos) = 1) then
    ref {n_comps = 1; comps = Array.create 1 (ref (nil_component())); env = nil_env(); fns = nil_fns()}
  else if (is_void_eqvar tau.tau_cont) && ((count_acts_comp p pos) = 1) then
    cut_comp p pos
  else
    (let tau_eq = 
      if is_void_eqvar tau.tau_cont then
	nil_eq()
      else
	Hashtbl.find !(!p.env) tau.tau_cont 
    in
    react_tau_pref_aux p pos ind tau_eq tau)

(***)

(*** Handles bound name output revelation ***)

let find_new_pos p old_ncomps old_ind =
  let res_comp = ref old_ncomps in
  let res_ind = ref old_ind in
  let i = ref (old_ncomps-1) in
  let found = ref false in
  while (!i < !p.n_comps) && (not !found) do
    if !res_ind < !(!p.comps.(!i)).nfnouts then
      (found := true;
       res_comp := !i);
    let ind_aux = ref !res_ind in
    if (not !found) then
      (try
	(List.iter (fun sum -> (match sum with(acts,taus,tests) ->
	  if !ind_aux < List.length acts then 
	    (found := true; 
	     res_comp := !i;
	     raise Found)
	  else
	    (ind_aux := !ind_aux - (List.length acts)))) !(!p.comps.(!i)).act_sums)
      with Found -> ignore 1);
    if (not !found) then
      (res_ind := !ind_aux - !(!p.comps.(!i)).nfnouts;
       incr i)
  done;
  (!res_comp,!res_ind)

(***)

(* Auxiliar function to find_name and find_action *)

let rec test_all l h =
  match l with
    [] -> (true,[])
  | Bname(x)::tl -> 
      let (res,resL) = test_all tl h in
      if res then
	(if not (Hashtbl.mem !h x) then
	  (Hashtbl.add !h x true;
	   (true,(fresh_name(),x)::resL))
	else
	  (true,resL))
      else
	(false,[])
  | Fname(x)::tl -> test_all tl h
  | Iname(i)::tl -> (false,[])

(***)

(*** Finds an action given the subject name ***)

let find_name p name act_t name_c name_i =
  let s1 = !p.n_comps in
  let found = ref false in
  let name_comp = ref name_c in
  let name_ind = ref name_i in
  let reveals = ref [] in
  while (!name_comp < s1) && (not !found) do
    let (s2,acts) = 
      if act_t = Inp_type then
	(!(!p.comps.(!name_comp)).nfninps,ref (!(!p.comps.(!name_comp)).fn_inps))
      else
	(!(!p.comps.(!name_comp)).nfnouts,ref (!(!p.comps.(!name_comp)).fn_outs))
    in
    while (!name_ind < s2) && (not !found) do
      found := name = get_string (!acts.(!name_ind).sub);
      (if (!found) && (act_t = Out_type) then
	(let (res,resL) = test_all !acts.(!name_ind).obj 
	    (ref (Hashtbl.create (List.length !acts.(!name_ind).obj))) in
	if res then
	  reveals := resL
	else
	  found := false));
      if not !found then
	incr name_ind
    done;
    (if not !found then
      let sum_ind = ref (!name_ind-s2) in
      try
	(List.iter (fun sum -> match sum with (acts,taus,tests) -> (List.iter
	    (fun act -> 
	      if !sum_ind = 0 then 
		(if (act_t = act.t) && (is_fn_act act) && (name = (get_string act.sub)) then
		  (if act_t = Out_type then
		    (let (res,resL) = test_all act.obj (ref (Hashtbl.create (List.length act.obj))) in
		    if res then
		      (found := true;
		       reveals := resL;
		       raise Found))
		  else
		    (found := true;
		     raise Found));
		 incr name_ind)
	      else
		decr sum_ind) acts)) !(!p.comps.(!name_comp)).act_sums)
      with Found -> ignore 1);
    if not !found then
      (incr name_comp;
       name_ind := 0);
  done;
  (!found,!name_comp,!name_ind,!reveals)

(***)

(*** Finds an action given the action type ***)

let find_action p act_t comp ind =
  let s1 = !p.n_comps in
  let found = ref false in
  let act_comp = ref comp in
  let act_ind = ref ind in
  let reveals = ref [] in
  while (!act_comp < s1) && (not !found) do
    let (s2,acts) = 
      if act_t = Inp_type then
	(!(!p.comps.(!act_comp)).nfninps,ref (!(!p.comps.(!act_comp)).fn_inps))
      else
	(!(!p.comps.(!act_comp)).nfnouts,ref (!(!p.comps.(!act_comp)).fn_outs))
    in
    while (!act_ind < s2) && (not !found) do
      (if act_t = Out_type then
	(let (res,resL) = test_all (!acts.(!act_ind).obj) (ref (Hashtbl.create (List.length !acts.(!act_ind).obj))) in
	if res then
	  (found := true;
	   reveals := resL))
      else
	found := true);
      if not !found then
	incr act_ind
    done;
    (if not !found then
      let sum_ind = ref (!act_ind-s2) in
      try
	(List.iter (fun sum -> match sum with (acts,taus,tests) -> (List.iter
	    (fun act -> 
	      if !sum_ind = 0 then 
		(if (act_t = act.t) && (is_fn_act act) then
		  (if act_t = Out_type then
		    (let (res,resL) = test_all act.obj (ref (Hashtbl.create (List.length act.obj))) in
		    if res then
		      (found := true;
		       reveals := resL;
		       raise Found))
		  else
		    (found := true;
		     raise Found));
		 incr act_ind)
	      else
		decr sum_ind) acts)) !(!p.comps.(!act_comp)).act_sums)
      with Found -> ignore 1);
    if not !found then
      (incr act_comp;
       act_ind := 0);
  done;
  (!found,!act_comp,!act_ind,!reveals)

(***)

(* Auxiliar function to next_react_aux *) 

let rec name_to_string l =
  match l with
    [] -> []
  | hd::tl -> (get_string hd)::(name_to_string tl)

(***)

(*** Returns a process where a transition on a subject name or action type has taken place ***)

let next_react_aux p act_t comp ind =
  if act_t = Inp_type then
    (let act = 
      if ind < !(!p.comps.(comp)).nfninps then
	!(!p.comps.(comp)).fn_inps.(ind)
      else
	get_act_sums !(!p.comps.(comp)).act_sums (ind- !(!p.comps.(comp)).nfninps) 0
    in
    react_label (act_t, get_string act.sub, fresh_names (List.length act.obj) 0) comp ind p)
  else
    (let act = 
      if ind < !(!p.comps.(comp)).nfnouts then
	!(!p.comps.(comp)).fn_outs.(ind)
      else
	get_act_sums !(!p.comps.(comp)).act_sums (ind- !(!p.comps.(comp)).nfnouts) 0
    in
    react_label (act_t, get_string act.sub, name_to_string act.obj) comp ind p)

(***)

(***)

(* Auxiliar function to congruent_n *)

let rec cut_supp l supp fix =
  match l with
    [] -> []
  | hd::tl -> 
      if (List.mem hd supp) || (List.mem hd fix) then
	cut_supp tl supp fix
      else
	hd::(cut_supp tl supp fix)

(***)

(* Auxiliar functions to is_cong_n_comp *)

let test_nums c1 c2 =
  (!c1.nrests = !c2.nrests) &&
  (!c1.nfnouts = !c2.nfnouts) &&
  (!c1.nbnouts = !c2.nbnouts) &&
  (!c1.nfninps = !c2.nfninps) &&
  (!c1.nbninps = !c2.nbninps) &&
  (!c1.ntests = !c2.ntests) &&
  (!c1.nsums = !c2.nsums)

(* Handle name relations *)

let rec cut_elem el l =
  match l with
    [] -> []
  | hd::tl -> if el = hd then tl else hd::(cut_elem el tl)

let rec related n1 n2 l =
  match l with
    [] -> ([],n1=n2)
  | (ns1,ns2)::tl -> 
      if List.mem n1 ns1 then
	(if List.mem n2 ns2 then
	  (if List.length ns1 = 1 then
	    (([n1],[n2])::tl,true)
	  else
	    (([n1],[n2])::((cut_elem n1 ns1, cut_elem n2 ns2)::tl),true))
	else
	  ((ns1,ns2)::tl,false))
      else
	(if List.mem n2 ns2 then
	  ((ns1,ns2)::tl,false)
	else
	  let (resL,res) = related n1 n2 tl in
	  ((ns1,ns2)::resL,res))

let relate_name n1 n2 fnames rests =
  match n1 with
    Fname(fn1) ->
      (match n2 with
	Fname(fn2) -> 
	  let (resL, res) = related fn1 fn2 !fnames in
	  fnames := resL;
	  res
      | _ -> false)
  | Bname(bn1) ->
      (match n2 with
	Bname(bn2) -> 
	  let (resL, res) = related bn1 bn2 !rests in
	  rests := resL;
	  res
      | _ -> false)
  | Iname(i) ->
      (match n2 with
	Iname(k) -> i = k
      | _ -> false)

let rec relate_nameL l1 l2 fnames rests =
  match l1 with
    [] -> true
  | hd::tl -> 
      (relate_name hd (List.hd l2) fnames rests) && 
      (relate_nameL tl (List.tl l2) fnames rests)

(* Handle sum comparison *)

let rec sums2ks acts taus tests =
	match acts with
	[] -> 
		(match taus with
		[] -> 
			(match tests with
			[] -> []
			|	hd::tail -> TestK(hd)::(sums2ks acts taus tail))
		|	hd::tail -> TauK(hd)::(sums2ks acts tail tests))
	|	hd::tail -> ActK(hd)::(sums2ks tail taus tests)


let select_sum_j nacts ntaus ntests i =
  if i < nacts then
    0
  else
    (if i - nacts < ntaus then
      nacts
    else
      nacts + ntaus)

let top_sum_j nacts ntaus ntests i =
  if i < nacts then
    nacts
  else
    (if i - nacts < ntaus then
      nacts + ntaus
    else
      nacts + ntaus + ntests)

(* Determines if two actions are equivalent *)

let rec is_cong_n_act k1 k2 fnames rests =
  match k1 with 
    ActK(act1) ->
    (match k2 with ActK(act2) ->
      if ((List.length act1.obj = List.length act2.obj) &&
	  (act1.cont = act2.cont) && (act1.t = act2.t) &&
	  (List.length act1.args = List.length act2.args)) then
	((relate_name act1.sub act2.sub fnames rests) &&
	 (relate_nameL act1.obj act2.obj fnames rests) &&
	 (relate_nameL act1.args act2.args fnames rests))
      else
	false
    | _ -> false)
  | TauK(tau1) ->
      (match k2 with TauK(tau2) ->
        if ((tau1.tau_cont = tau2.tau_cont) &&
	    (List.length tau1.tau_args = List.length tau2.tau_args)) then
	  (relate_nameL tau1.tau_args tau2.tau_args fnames rests)
	else
	  false
      | _ -> false)
  | TestK(test1) ->
      (match k2 with TestK(test2) ->
	if ((test1.tcont = test2.tcont) &&
	    (List.length test1.targs = List.length test2.targs)) then
	  (((test1.idl = test2.idl) = (test1.idr = test2.idr)) &&
	   (relate_nameL test1.targs test2.targs fnames rests))
	else
	  false
      | _ -> false)
  | SumK(sum1) ->
      (match k2 with SumK(sum2) ->
        (match sum1 with (acts1,taus1,tests1) ->
	match sum2 with (acts2,taus2,tests2) ->
	(let size1acts = List.length acts1 in
	let size2acts = List.length acts2 in
	if (size1acts <> size2acts) then
	  false
	else
	  (let sum_vec1 = Array.of_list acts1 in
	  let sum_vec2 = Array.of_list acts2 in
	  let corresp = Array.create (size1acts) (-1) in
	  let marker = Array.create (size2acts) false in
	  let i = ref 0 in
	  let j = ref 0 in
	  let backup_fnames = Array.create (size1acts + 1) [] in
	  let backup_rests = Array.create (size2acts + 1) [] in
	  backup_fnames.(0) <- !fnames;
	  backup_rests.(0) <- !rests;
	  let res = ref true in
	  (try
	    while !i < size1acts do
	      if ((not marker.(!j)) &&
	          (is_cong_n_act (ActK(sum_vec1.(!i))) (ActK(sum_vec2.(!j))) fnames rests)) then
		(corresp.(!i) <- !j;
		marker.(!j) <- true;
		incr i;
		backup_fnames.(!i) <- !fnames;
		backup_rests.(!i) <- !rests;
		j := 0)
	      else
	        (if !j < size1acts - 1 then
		  incr j
		else
		  (while (!j = size1acts - 1) && (!i > 0) do
		    fnames := (backup_fnames.(!i));
		    rests := (backup_rests.(!i));
		    decr i;
		    j := corresp.(!i);
		    marker.(!j) <- false;
		    corresp.(!i) <- -1;
		  done;
		  if !i = 0 then
		    raise False
		  else
		    incr j))
	    done;
	with False -> (fnames := (backup_fnames.(0)); res := false));
        !res)))
      | _ -> false)
	
(* Auxiliar functions to is_cong_n_comp *)

let select_act c i =
  if i < !c.nfnouts then
    ActK(!c.fn_outs.(i))
  else
    (let j = i - !c.nfnouts in
    if j < !c.nbnouts then
      ActK(!c.bn_outs.(j))
    else
      (let k = j - !c.nbnouts in
      if k < !c.nfninps then
	ActK(!c.fn_inps.(k))
      else
	(let m = k - !c.nfninps in
	if m < !c.nbninps then
	  ActK(!c.bn_inps.(m))
	else
	  (let n = m - !c.nbninps in
	  if n < !c.ntests then
	    TestK(!c.id_tests.(n))
	  else 
	    (let l = n - !c.ntests in
	    if l < !c.ntaus then
		TauK(!c.act_taus.(l))
	    else
		SumK(List.nth !c.act_sums (l - !c.ntaus)))))))

let select_j c i =
  if i < !c.nfnouts then
    0
  else
    (let k = (i- !c.nfnouts) in
    if k < !c.nbnouts then
      !c.nfnouts
    else
      (let n = (k- !c.nbnouts) in
      if n < !c.nfninps then
	(!c.nfnouts+ !c.nbnouts)
      else
	(let m = (n - !c.nfninps) in
	if m < !c.nbninps then
	  (!c.nfnouts+ !c.nbnouts+ !c.nfninps)
	else
	  (let l = (m - !c.nbninps) in
	  if l < !c.ntests then
	    (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps)
	  else
	    (let o = (l - !c.ntests) in
	    if o < !c.ntaus then
	      (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps + !c.ntests)
	    else
	      (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps + !c.ntests + !c.ntaus))))))

let top_j c i =
  if i < !c.nfnouts then
    !c.nfnouts
  else
    (let k = (i- !c.nfnouts) in
    if k < !c.nbnouts then
      (!c.nfnouts+ !c.nbnouts)
    else
      (let n = (k- !c.nbnouts) in
      if n < !c.nfninps then
	(!c.nfnouts+ !c.nbnouts+ !c.nfninps)
      else
	(let m = (n - !c.nfninps) in
	if m < !c.nbninps then
	  (!c.nfnouts+ !c.nbnouts+ !c.nfninps + !c.nbninps)
	else
	  (let l = (m - !c.nbninps) in
	  if l < !c.ntests then
	    (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps + !c.ntests)
	  else
	    (let o = (l - !c.ntests) in
	    if o < !c.ntaus then
	      (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps + !c.ntests + !c.ntaus)
	    else
	      (!c.nfnouts + !c.nbnouts + !c.nfninps + !c.nbninps + !c.ntests + !c.ntaus + !c.nsums))))))

(* Determines if two components are equivalent *)

let is_cong_n_comp p1 p2 i j fnames = 
  let c1 = !p1.comps.(i) in
  let c1_num_acts = count_acts_comp p1 i in
  let c2 = !p2.comps.(j) in
  let c2_num_acts = count_acts_comp p2 j in
  if not (test_nums c1 c2) then
    false
  else
    (let rests = ref [(get_stringL (Array.to_list !c1.rests), 
		       get_stringL (Array.to_list !c2.rests))] in
    let corresp = Array.create (c1_num_acts) (-1) in
    let marker = Array.create (c2_num_acts) false in
    let i = ref 0 in
    let j = ref (select_j c2 !i) in
    let backup_fnames = Array.create (c1_num_acts+1) [] in
    let backup_rests = Array.create (c1_num_acts+1) [] in
    backup_fnames.(0) <- !fnames;
    backup_rests.(0) <- !rests;
    let res = ref true in
    (try
      while !i < c1_num_acts do
	if ((not marker.(!j)) && 
	    (is_cong_n_act (select_act c1 !i) (select_act c2 !j) fnames rests)) then
	  (corresp.(!i) <- !j;
	   marker.(!j) <- true;
	   incr i;
	   backup_fnames.(!i) <- !fnames;
	   backup_rests.(!i) <- !rests;
	   j := select_j c2 !i)
	else
	  (if !j < (top_j c2 !i)-1 then
	    incr j
	  else
	    (while (!j = (top_j c2 !i)-1) && (!i > 0) do
	      fnames := (backup_fnames.(!i));
	      rests := (backup_rests.(!i));
	      decr i;
	      j := corresp.(!i);
	      marker.(!j) <- false;
	      corresp.(!i) <- -1;
	    done;
	     if !i = 0 then
	       raise False
	     else
	       incr j))
      done;
    with False -> (fnames := (backup_fnames.(0)); res := false));
    !res)

(* Auxiliar functions and variables to congruent_n *)

let rec singles l l2 =
  match l with
    [] -> l2
  | hd::tl -> ([hd],[hd])::(singles tl l2)

let glob_supp: string list ref = ref []
let glob_fix: string list ref = ref []

let rec match_args args1 args2 el = 
  match args1 with 
    [] -> [el]
  | hd::tl -> ([hd],[List.hd args2])::(match_args tl (List.tl args2) el)

(* Determines if two processes are equivalent *)

let congruent_n val1 val2 =
  match val1 with (p1,p1_args) ->
    match val2 with (p2,p2_args) ->
      (let supp = !glob_supp in
      if (num_comps p1) <> (num_comps p2) then
	false
      else
	(let fn_p1 = free_names p1 in
	let fn_p2 = free_names p2 in
	let fn_p1_supp = cut_supp fn_p1 supp p1_args in
	let fn_p2_supp = cut_supp fn_p2 supp p2_args in
	if (((List.length fn_p1) <> (List.length fn_p2))
	  || ((List.length fn_p1_supp) <> (List.length fn_p2_supp))) then
	  false
	else
	  (let fixed = match_args p1_args p2_args (fn_p1_supp,fn_p2_supp) in
	  let fnames = ref (singles supp fixed) in
	  let corresp = Array.create (num_comps p1) (-1) in
	  let marker = Array.create (num_comps p2) false in
	  let backup_fnames = Array.create (1+(num_comps p1)) [] in
	  backup_fnames.(0) <- !fnames;
	  let i = ref 0 in
	  let j = ref 0 in
	  let res = ref true in
	  (try
	    while !i < (num_comps p1) do
	      if ((not marker.(!j)) &&
		  (is_cong_n_comp p1 p2 !i !j fnames)) then
		(corresp.(!i) <- !j;
		 marker.(!j) <- true;
		 incr i;
		 backup_fnames.(!i) <- !fnames;
		 j := 0)
	      else
		(if !j < (num_comps p2)-1 then
		  incr j
		else
		  (while (!j = (num_comps p2)-1) && (!i > 0) do
		    fnames := (backup_fnames.(!i));
		    decr i;
		    j := corresp.(!i);
		    marker.(!j) <- false;
		    corresp.(!i) <- -1;
		  done;
		   if !i = 0 then
		     raise False
		   else
		     incr j))
	    done;
	  with False -> res := false);
	  !res)))
	  
(***)

(* Hash function for processes *)

let hash_comps p =
  let res = ref 0 in
  let hash_val = Hashtbl.hash "$x" in
  for i= 0 to (num_comps p)-1 do
    let comp = (!p.comps.(i)) in
    for j = 0 to !comp.nfnouts-1 do
      res := !res+ !comp.fn_outs.(j).cont + hash_val
    done;
    for j = 0 to !comp.nfninps-1 do
      res := !res+ !comp.fn_inps.(j).cont + hash_val
    done;
    for j = 0 to !comp.nbnouts-1 do
      res := !res+ !comp.bn_outs.(j).cont + hash_val
    done;
    for j = 0 to !comp.nbninps-1 do
      res := !res+ !comp.bn_inps.(j).cont + hash_val
    done;
    for j = 0 to !comp.ntests-1 do
      res := !res+ !comp.id_tests.(j).tcont + hash_val
    done;
    for j = 0 to !comp.ntaus-1 do
      res := !res+ !comp.act_taus.(j).tau_cont + hash_val
    done;
    List.iter (fun sum -> (match sum with (acts,taus,tests) ->
      List.iter (fun act -> res := !res+ act.cont + hash_val) acts;
      List.iter (fun tau -> res := !res+ tau.tau_cont + hash_val) taus;
      List.iter (fun test -> res := !res+ test.tcont + hash_val) tests)) !comp.act_sums;
  done;
  !res

(***)

(*** Top level process set type ***)

module Process_hash = 
  struct
    type t = process * string list
    let equal p1 p2 = congruent_n p1 p2
    let hash p = match p with (proc,l) -> ((num_comps proc)*(hash_comps proc))
  end;;

module Process_set = Hashtbl.Make(Process_hash)

type process_set = bool Process_set.t

(*** Creates a process set ***)

let create_pset p l =
  let pset = Process_set.create 100 in
  Process_set.add pset (p,l) true;
  pset

(***)
  
(*** Adds a process to a process set ***)

let add_to_pset pset p l =
  Process_set.add pset (p,l) true

(***)

(*** Removes a process from a process set ***)

let remove_from_pset pset p l =
  Process_set.remove pset (p,l)

(***)

(*** Determines if there exists an equivalent process in the process set ***)

let rec exists_congruent_n p l pset supp =
  glob_supp := supp;
  let res = Process_set.mem pset (p,l) in
  glob_supp := [];
  res

(***)
