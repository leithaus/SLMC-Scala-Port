(*** Module that handles the search algorithms for process inspections ***)

open Namegen
open Piastnode
open Process

(***)

exception No_more_comps

exception No_more_reveals

exception No_more_reacts

(***)

(* Iterator status type *)

type it_status = Not_finished | Dummy of bool | Finished

(* Internal silent action type *)

type tau_stat = Fn_synch | Bn_synch | Test_act | Tau_act

(*** Iterator type for composition ***)

type comp_it = 
    {comp_p: process; 
     mutable comp_status: it_status;
     mutable comp_num: int;
     mutable comp_list: int list}

(*** Iterator type for revelation ***)

type reveal_it =
    {reveal_p: process;
     reveal_n: string;
     mutable rev_status: it_status;
     mutable rev_pos: int;
     mutable rev_index: int}

(*** Reaction label type ***)

type react_label = 
    Tau 
  | Lab of Process.label 
  | Name of string * Equations.action_type
  | Action of Equations.action_type

(* Iterator type for internal action *)

type tau_it = 
    {mutable tau_status: tau_stat;
     mutable inp_comp: int; 
     mutable inp_ind: int; 
     mutable out_comp: int; 
     mutable out_ind: int;
     mutable tes_comp: int;
     mutable tes_ind: int;
     mutable tau_comp: int;
     mutable tau_ind: int}

(* Iterator type for label reaction *)

type lab_it = 
    {lab: Process.label; 
     marker: bool array;
     mutable cur_comp: int; 
     mutable cur_ind: int}

(* Iterator type for name reaction *)

type name_it =
    {name: string;
     name_act: Equations.action_type;
     mutable name_comp: int;
     mutable name_ind: int}

(* Iterator type for kind reaction *)

type action_it =
    {act_t: Equations.action_type;
     mutable act_comp: int;
     mutable act_ind: int}

(* Iterator type bundle *)

type it_info = 
    Tau_info of tau_it 
  | Lab_info of lab_it 
  | Name_info of name_it 
  | Action_info of action_it

(*** Iterator type for reactions ***)

type react_it = 
    {react_p: process; 
     info: it_info}

(***)

(*** Returns the composition iterator ***)

let comp p =
  let size = (num_comps p) in
  let sta = 
    (if size = 1 then
      Dummy(empty_proc p)
    else 
      Not_finished) in
  {comp_p= p; comp_status = sta; comp_num= 1; comp_list=[size-1]}

(***)

(* Auxiliar functions to next_comp *)

let rec last_pos k l =
  match l with
    [] -> false
  | hd::[] ->
      (hd = k)
  | hd::tl ->
      (hd = k) && (last_pos (k+1) tl)

let rec create_list k s =
  let res = ref [] in
  for i = 0 to s-1 do
    res := (k-i)::(!res)
  done;
  !res

let rec dec_list l k =
  match l with 
    [] -> []
  | hd::[] -> 
      k := hd-2;
      (hd-1)::[]
  | hd::tl -> 
      if hd > !k then 
	(k := hd-2;
	 (hd-1)::tl)
      else 
	(incr k;
	 let ntl = dec_list tl k in
	 let nhd = !k in
	 decr k;
	 nhd::ntl)

(***)

let comp_info it size =
  let last = last_pos 0 it.comp_list in
  if last && (it.comp_num = size-1) then
    it.comp_status <- Dummy(false)
  else
    (if last then
      (it.comp_num <- it.comp_num+1;
       it.comp_list <- create_list (size-1) it.comp_num)
    else
      it.comp_list <- dec_list it.comp_list (ref 0))

(*** Returns the iterator's next composition of processes ***)

let next_comp it =
  match it.comp_status with
    Not_finished ->
      let size = (num_comps (it.comp_p)) in
      let comp_num = it.comp_num in
      let nl = it.comp_list in
      comp_info it size;
      extract_comps (it.comp_p) nl size comp_num (size-comp_num)
  | Dummy(b) ->
      if b then
	(it.comp_status <- Finished;
	 comp_empty it.comp_p true)
      else
	(it.comp_status <- Dummy(true);
	 comp_empty it.comp_p false)
  | Finished ->
      raise No_more_comps

(***)
	  
(*** Returns the revelation iterator ***)

let reveal p revn =
  if (test_fn p revn) then
    {reveal_p = p; reveal_n= revn; rev_status = Finished; rev_pos = 0; rev_index=0}
  else
    let ind = find_res p 0 in
    let sta = (if (ind = num_comps p) then Dummy(false) else Not_finished) in
    {reveal_p = p; reveal_n = revn; rev_status = sta; rev_pos= ind; rev_index= 0}

(***)

(* Auxiliar function to next_reveal *)

let rev_info it =
  if (nrests_comp it.reveal_p it.rev_pos) = it.rev_index+1 then
    (let new_pos = find_res it.reveal_p (it.rev_pos+1) in
    if new_pos = num_comps (it.reveal_p) then
      it.rev_status <- Dummy(false)
    else
      (it.rev_pos <- new_pos;
      it.rev_index <- 0))
  else
    it.rev_index <- it.rev_index +1
 
(*** Returns the iterator's next revelation process ***)

let next_reveal it =
  match it.rev_status with
    Not_finished ->
      let pos = it.rev_pos in
      let ind = it.rev_index in
      rev_info it;
      rev_comps it.reveal_p pos ind it.reveal_n
  | Dummy(b) ->
      it.rev_status <- Finished;
      (it.reveal_p)	
  | Finished -> 
      raise No_more_reveals

(***)

(*** Returns the reaction iterator ***)

let react p a =
  let info_aux = 
    (match a with 
      Tau -> Tau_info({tau_status = Fn_synch; inp_comp= 0; inp_ind=0; out_comp=0; 
		       out_ind= 0; tes_comp=0; tes_ind=0; tau_comp =0; tau_ind = 0})
    | Lab(t, sub, obj) -> 
	let fns =
	  if t = Equations.Out_type then
	    let fns_p = free_names p in
	    let i = ref 0 in 
	    let fresh_ns = Array.create (List.length obj) false in
	    List.iter 
             (fun id -> 
                 (if (id = "_") || not (List.mem id fns_p) then (fresh_ns.(!i) <- true)); 
                 incr i) 
             obj;
	    fresh_ns
	  else
	    Array.create 0 false
	in
	Lab_info({lab= (t,sub,obj); marker = fns; cur_comp= 0; cur_ind=0})
    | Name(n, a) -> Name_info({name = n; name_act = a; name_comp = 0; name_ind =0})
    | Action(a) -> Action_info({act_t= a; act_comp = 0; act_ind=0}))
  in {react_p = p; info= info_aux}

(***)

(*** Returns the next reaction process ***) 

let rec next_react it =
  match it.info with
    Lab_info(i) ->
      let (not_found,comp,ind,reveals) = 
	find_label it.react_p i.lab i.cur_comp i.cur_ind i.marker in
      (if not_found then
	raise No_more_reacts);
      i.cur_comp <- comp;
      i.cur_ind <- ind+1;
      let ptr_p = ref (it.react_p) in
      let res_name_comp = ref comp in
      let res_name_ind = ref ind in
      List.iter 
	(fun arg -> 
	  match arg with (newn,oldn) -> 
	    let old_ncomps = num_comps !ptr_p in
	    let rest_ind = find_rest (!ptr_p) !res_name_comp oldn in
	    ptr_p := rev_comps (!ptr_p) !res_name_comp rest_ind newn;
	    let (new_name_comp,new_name_ind) = find_new_pos !ptr_p old_ncomps !res_name_ind in
	    res_name_comp := new_name_comp;
	    res_name_ind := new_name_ind) 
	reveals;
      react_label i.lab !res_name_comp !res_name_ind !ptr_p
  | Tau_info(i) ->
      if i.tau_status = Fn_synch then
	(let (not_found,inp_comp,inp_ind,out_comp,out_ind) = 
	  find_fn_tau it.react_p i.inp_comp i.inp_ind i.out_comp i.out_ind in
	if not_found then
	  (i.tau_status <- Bn_synch;
	   i.inp_comp <- 0;
	   i.inp_ind <- 0;
	   i.out_comp <- 0;
	   i.out_ind <- 0;
	   next_react it)
	else
	  (i.inp_comp <- inp_comp;
	   i.inp_ind <- inp_ind;
	   i.out_comp <- out_comp;
	   i.out_ind <- out_ind+1;
	   react_tau i.inp_comp i.inp_ind i.out_comp out_ind true it.react_p))
      else if i.tau_status = Bn_synch then
	(let (not_found,comp,inp_ind,out_ind) = 
	  find_bn_tau it.react_p i.inp_comp i.inp_ind i.out_ind in
	if not_found then
	  (i.tau_status <- Test_act;
	   next_react it)
	else
	  (i.inp_comp <- comp;
	   i.inp_ind <- inp_ind;
	   i.out_ind <- out_ind+1;
	   react_tau i.inp_comp i.inp_ind i.inp_comp out_ind false it.react_p))
      else if i.tau_status = Test_act then
	(let (found,comp,ind) = find_test it.react_p i.tes_comp i.tes_ind in
	if not found then
	  (i.tau_status <- Tau_act;
	  next_react it)
	else
	  (i.tes_comp <- comp;
	   i.tes_ind <- ind+1;
	   react_test comp ind it.react_p))
      else
        (let (found,comp,ind) = find_tau_pref it.react_p i.tau_comp i.tau_ind in
	(if not found then
	  raise No_more_reacts);
	i.tau_comp <- comp;
	i.tau_ind <- ind+1;
	react_tau_pref comp ind it.react_p)
  | Name_info(i) ->
      let (found,comp,ind,reveals) = find_name it.react_p i.name i.name_act i.name_comp i.name_ind in
      (if not found then
	raise No_more_reacts);
      i.name_comp <- comp;
      i.name_ind <- ind+1;
      let ptr_p = ref (it.react_p) in
      let res_name_comp = ref comp in
      let res_name_ind = ref ind in
      List.iter 
	(fun arg -> 
	  match arg with (newn,oldn) -> 
	    let old_ncomps = num_comps !ptr_p in
	    let rest_ind = find_rest (!ptr_p) !res_name_comp oldn in
	    ptr_p := rev_comps (!ptr_p) !res_name_comp rest_ind newn;
	    let (new_name_comp,new_name_ind) = find_new_pos !ptr_p old_ncomps !res_name_ind in
	    res_name_comp := new_name_comp;
	    res_name_ind := new_name_ind) 
	reveals;
      next_react_aux !ptr_p i.name_act !res_name_comp !res_name_ind
  | Action_info(i) ->
      let (found,comp,ind,reveals) = find_action it.react_p i.act_t i.act_comp i.act_ind in
      (if not found then
	raise No_more_reacts);
      i.act_comp <- comp;
      i.act_ind <- ind+1;
      let ptr_p = ref (it.react_p) in
      let res_name_comp = ref comp in
      let res_name_ind = ref ind in
      List.iter 
	(fun arg -> 
	  match arg with (newn,oldn) -> 
	    let old_ncomps = num_comps !ptr_p in
	    let rest_ind = find_rest (!ptr_p) !res_name_comp oldn in
	    ptr_p := rev_comps (!ptr_p) !res_name_comp rest_ind newn;
	    let (new_name_comp,new_name_ind) = find_new_pos !ptr_p old_ncomps !res_name_ind in
	    res_name_comp := new_name_comp;
	    res_name_ind := new_name_ind) 
	reveals;
      next_react_aux !ptr_p i.act_t !res_name_comp !res_name_ind

(***)
