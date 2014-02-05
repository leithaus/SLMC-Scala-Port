(*** Abstract syntactic tree representation for CC processes ***)

open Piastnode
open Namegen

exception Ill_formed_ast_cc

type direction = Here | Up 

(*** Action type ***)
type ccaction = 
    CCInput of direction * string * (string list)
  | CCOutput of direction * string * string list

type ccastnode = 
    CCInact 
  | CCPar of ccastnode  * ccastnode 
  | CCSum of ccastnode list
  | CCCxt of string * ccastnode
  | CCThis of string * ccastnode
  | CCAct of ccaction * ccastnode
  | CCDef of string * ccastnode 
  | CCNew of string * string * ccastnode 
  | CCJoin of string * string * ccastnode
  | CCVar of string * string list
  | CCIfThenElse of ccastnode  * ccastnode

(*** Declaration environment type ***)
type cc_dec = Ccdec of string * string list * ccastnode 

let rec print_ccargs l =
  match l with
    [] -> print_string ""
  | hd::[] -> print_string hd
  | hd::tl -> print_string hd; print_string ","; print_ccargs tl

let print_ccact act =
   match act with
    CCInput(dir, label, args) ->
      if dir = Here then
        (print_string label;
	print_string "?(";
        print_ccargs args;
	print_string ").")
      else
       (print_string label;
	print_string "^?(";
        print_ccargs args;
	print_string ").")
|   CCOutput(dir, label, args) ->
      if dir = Here then
        (print_string label;
	print_string "!(";
        print_ccargs args;
	print_string ").")
      else
       (print_string label;
	print_string "^!(";
        print_ccargs args;
	print_string ").")

let rec print_ccast ast = 
  match ast with
    CCInact -> 
      print_string "end"
  | CCPar(ast1, ast2) -> 
      print_string "(";
      print_ccast ast1;
      print_newline(); 
      print_string " | "; 
      print_newline(); 
      print_ccast ast2;
      print_string ")"
  | CCSum(astl) -> 
      print_string "switch {";
      print_newline(); 
      print_ccastlist astl; 
      print_string "}";
      print_newline()
  | CCCxt(conv, ast) ->
      print_string "context ";
      print_string conv;
      print_string " {";
      print_newline();
      print_ccast ast;
      print_string "} "
  | CCThis(thisvar, ast) ->
      print_string "this(";
      print_string thisvar;
      print_string ").";
      print_newline(); 
      print_ccast ast;
  | CCAct(ccact, ast) ->
      print_ccact ccact;
      print_newline(); 
      print_ccast ast
  | CCDef(label,ast) ->
      print_string "def ";
      print_string label;
      print_string " => (";
      print_newline(); 
      print_ccast ast;
      print_string ") " 
  | CCNew(conv,label,ast) ->
      print_string "new ";
      print_string conv;
      print_string ".";
      print_string label;
      print_string " <= (";
      print_newline(); 
      print_ccast ast;
      print_string ") "
  | CCJoin(conv,label,ast) ->
      print_string "join ";
      print_string conv;
      print_string ".";
      print_string label;
      print_string " <= (";
      print_newline(); 
      print_ccast ast;
      print_string ") "
  | CCVar(rvar,ids) ->
      print_string rvar;
      print_string "(";
      print_ccargs ids;
      print_string ")"
  | CCIfThenElse(astt,aste) ->
      print_string "if (cond) then ";
      print_newline(); 
      print_ccast astt;
      print_newline(); 
      print_string "else ";
      print_newline(); 
      print_ccast aste
and print_ccastlist l =
  match l with
    [] -> print_string ""
  | hd::[] -> print_ccast hd; print_newline()
  | hd::tl -> print_ccast hd; print_string ";"; print_newline(); print_ccastlist tl

let rec testids ids1 ids2 =
match ids1 with [] -> 
	(match ids2 with 
	  [] -> true 
	| hd::tl -> false)
| hd::tl -> 
	(match ids2 with 
	  [] -> false 
	| hd2::tl2 -> ((hd = hd2) && testids tl tl2)
)


let rec translate_ccast ccproc upconv hereconv recaux =
  match ccproc with
    CCInact -> 
      ref Void
  | CCPar(ast1, ast2) -> 
      ref (Par(translate_ccast ast1 upconv hereconv recaux,
	      translate_ccast ast2 upconv hereconv recaux))
  | CCSum(astl) -> 
	let labelx = fresh_name() in
	let f = fresh_name() in
      let (selast,dir,args) = translate_ccastlist astl upconv hereconv labelx f recaux in
      let conv = (if dir = Here then hereconv else upconv) in
        ref (Act(Input(conv,labelx::(f::args)), selast))
  | CCCxt(conv, ast) ->
      translate_ccast ast hereconv conv recaux
  | CCThis(thisvar, ast) ->
	let nonce = fresh_name() in
     ref (New([nonce],
			ref (Act(Tau, ref (Act(Tau, ref (Par(ref (Act(Output(nonce,[hereconv]), ref Void)),
										        ref (Act(Input(nonce,[thisvar]),
																	translate_ccast ast upconv hereconv recaux))))))))))
  | CCAct(ccact, ast) ->
	  translate_ccact ccact ast upconv hereconv recaux
  | CCDef(label,ast) ->
      let labelx = fresh_name() in
      let f = fresh_name() in
      let conv = fresh_name() in
        (ref (Act(Input(hereconv,labelx::(f::[conv])),
                 ref (Test(labelx, label,
                          ref (Par(ref (Act(Input(f,[]), 
						ref (Par(translate_ccast ast hereconv conv recaux, ref (recaux))))),
			                       ref (Act(Output(f,[]), ref Void)))),Equals)))))
  | CCNew(conv,label,ast) ->
      let f = fresh_name() in
      let fconv = fresh_name() in
        (ref (New(f::[fconv],ref (Act(Output(conv,label::(f::[fconv])), translate_ccast ast hereconv fconv recaux)))))
  | CCJoin(conv,label,ast) ->
      let f = fresh_name() in
        (ref (New([f],ref (Act(Output(conv,label::(f::[hereconv])), translate_ccast ast upconv hereconv recaux)))))
  | CCVar(rvar,ids) ->
	  ref (Var(rvar,upconv::(hereconv::ids)))
  | CCIfThenElse(astt,aste) ->
	let nonce = fresh_name() in
     ref (New([nonce], 
			ref (Act(Tau, ref (Sum( ref (Act(Tau, ref (Par(ref (Act(Output(nonce,[]), ref Void)),
														 ref (Act(Input(nonce,[]),
																	translate_ccast astt upconv hereconv recaux)))))),
									ref (Act(Tau, ref (Par(ref (Act(Output(nonce,[]), ref Void)),
														   ref (Act(Input(nonce,[]),
																	translate_ccast aste upconv hereconv recaux))))))))))))

and translate_ccastlist l upconv hereconv labelx f recaux =
  match l with
    [] -> (ref Void,Here,[])
  | hd::[] -> (match hd with CCAct(CCInput(dir, label, args), ast) -> 
		(ref (Test(labelx, label,
                          ref (Par(ref (Act(Input(f,[]), translate_ccast ast upconv hereconv recaux)),
			          ref (Act(Output(f,[]), ref Void)))),Equals))
			,dir,args)
              | _ -> raise Ill_formed_ast_cc)
  | hd::tl -> let (left,dir1,args1) = translate_ccastlist tl upconv hereconv labelx f recaux in
              (match hd with CCAct(CCInput(dir, label, args), ast) -> 
		if (dir = dir1) && (testids args args1) then
		  (ref (Sum (left, 
			ref (Test(labelx, label,
                          ref (Par(ref (Act(Input(f,[]), translate_ccast ast upconv hereconv recaux)),
			          ref (Act(Output(f,[]), ref Void)))),Equals)))),dir,args)
                else 
		  raise Ill_formed_ast_cc
              | _ -> raise Ill_formed_ast_cc)
			  
and translate_ccact act ast upconv hereconv recaux =
   match act with
    CCInput(dir, label, args) ->
      let labelx = fresh_name() in
      let f = fresh_name() in
      let conv = (if dir = Here then hereconv else upconv) in
        (ref (Act(Input(conv,labelx::(f::args)),
                 ref (Test(labelx, label,
                          ref (Par(ref (Act(Input(f,[]), translate_ccast ast upconv hereconv recaux)),
			                      ref (Act(Output(f,[]), ref Void)))),Equals)))))
|   CCOutput(dir, label, args) ->
      let f = fresh_name() in
      let conv = (if dir = Here then hereconv else upconv) in
        (ref (New([f],ref (Act(Output(conv,label::(f::args)), translate_ccast ast upconv hereconv recaux)))))
