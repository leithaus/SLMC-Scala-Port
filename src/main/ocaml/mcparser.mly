/* Parser for the model checker top level */

  %{

open Piastnode
open Formastnode
open Ccastnode

let names = Hashtbl.create 11
let usage = Hashtbl.create 53

    %}  
  
    %token <string> ID CAPS_ID FILENAME
    %token <int> INT
    %token USCORE
    %token NEW REC IN
    %token BANG QUESTION
    %token PIPE DOT ZERO
    %token SELECT LBR RBR
    %token LPAR RPAR COMMA 
    %token TRUE FALSE 
    %token DBLPIPE VOID 
    %token AND OR NOT DEQ NEQ IMPLIES EQUIV
    %token REVEAL LT GT LPARR RPARR TAU STAR
    %token FRESH HIDDEN REVEALALL FREE
    %token EXISTS FORALL MAXFIX MINFIX ALWAYS EVENTUALLY INSIDE
    %token SHOW_F SHOW_S
    %token DEFPROC AND EQ DEFPROP CONV DEFARROW PI SL CDL
    %token CHECK PROCS PROPS SAT 
    %token CD PD TRACE ON OFF PRINT SHOW
    %token QUIT SEMI LOAD HELP CLEAR PARAM MT CC ST
    %token DEFC CTX JOIN UPC SWITCH IF THEN ELSE THIS END CHOICE EXCHANGE
    %token EOF
    %left PIPE DBLPIPE
    %left IMPLIES EQUIV
    %left OR
    %left AND
    %nonassoc NOT
    
    %type <Mcmenu.menu> main

    %start main
      
    %%
  
  main:
    def_proc      SEMI { Mcmenu.Defproc($1) }
|   def_prop      SEMI { Mcmenu.Defprop($1) }
|   check         SEMI { Mcmenu.Check($1) }
|   PARAM MT INT  SEMI { Mcmenu.DefMaxThreads($3) }
|   PARAM MT      SEMI { Mcmenu.PrintMaxThreads }
|   PARAM CC ON   SEMI { Mcmenu.DefCheckCounter(true) }
|   PARAM CC OFF  SEMI { Mcmenu.DefCheckCounter(false) }
|   PARAM CC      SEMI { Mcmenu.PrintCheckCounter }
|   PARAM ST ON   SEMI { Mcmenu.DefShowTime(true) }
|   PARAM ST OFF  SEMI { Mcmenu.DefShowTime(false) }
|   PARAM ST      SEMI { Mcmenu.PrintShowTime }
|   PARAM         SEMI { Mcmenu.ListParams }
|   CD FILENAME   SEMI { Mcmenu.CD($2) }
|   PD            SEMI { Mcmenu.PD }
|   TRACE         SEMI { Mcmenu.PrintTrace }
|   TRACE ON      SEMI { Mcmenu.DefTrace(true) }
|   TRACE OFF     SEMI { Mcmenu.DefTrace(false) }
|   LOAD FILENAME SEMI { Mcmenu.Load($2) }
|   CLEAR         SEMI { Mcmenu.Clear }
|   SHOW CAPS_ID  SEMI { Mcmenu.ShowProc($2) }
|   SHOW ID       SEMI { Mcmenu.ShowProp($2) }
|   PRINT PROCS   SEMI { Mcmenu.PrintProcs }
|   PRINT PROPS   SEMI { Mcmenu.PrintProps }
|   HELP          SEMI { Mcmenu.Help }
|   SEMI               { Mcmenu.Continue }
|   QUIT          SEMI { Mcmenu.Done }
|   EOF                { Mcmenu.Done }
|   error         SEMI { raise (Checker.ErrorMsg ("defproc\ndefprop\ncheck\nparameter\nlist\nshow\nload\ncd\npd\n"^
                                                  "trace\nclear\nhelp\nquit")) }
    ;

  check:
    CHECK CAPS_ID check_args SAT form { ($2,$3,$5) }
|   CHECK CAPS_ID check_args SAT error { raise (Checker.ErrorMsg "<FORMULA>") }
|   CHECK CAPS_ID error { raise (Checker.ErrorMsg "|=\n(") }
|   CHECK error { raise (Checker.ErrorMsg "<PROCESS IDENTIFIER>") }
    ;

  def_proc:
     DEFPROC CONV CAPS_ID params EQ proc_cc 
        { Mcmenu.CCProcdec(Ccdec($3,$4,$6)) }
|    DEFPROC PI CAPS_ID params EQ proc ands { let (r1,r2,r3) = $7 in Mcmenu.PIProcdec(Pidec($3::r1,$4::r2, $6::r3)) }
|    DEFPROC CAPS_ID params EQ proc ands { let (r1,r2,r3) = $6 in Mcmenu.PIProcdec(Pidec($2::r1,$3::r2, $5::r3)) }
|   DEFPROC CAPS_ID params EQ proc error { raise (Checker.ErrorMsg "and\n;\n|") }
|   DEFPROC CAPS_ID params EQ error { raise (Checker.ErrorMsg "<PROCESS>") }
|   DEFPROC CAPS_ID error {raise (Checker.ErrorMsg "=\n(") }
|   DEFPROC error { raise (Checker.ErrorMsg "<PROCESS IDENTIFIER>") } 
    ;

  ands:
    { ([], [], []) }
|   ands AND CAPS_ID params EQ proc { let (r1,r2,r3) = $1 in ($3::r1,$4::r2,$6::r3) }
|   ands AND CAPS_ID params EQ error { raise (Checker.ErrorMsg "<PROCESS>") }
|   ands AND CAPS_ID error { raise (Checker.ErrorMsg "=\n(") }
    ;

  params:
                  { [] }
|   LPAR RPAR     { [] }
|   LPAR param_ids RPAR { List.rev $2 }
|   LPAR error    { raise (Checker.ErrorMsg "<ID> [,<ID>]*\n)") }
    ;

  check_args: 
    { [] }
|   LPAR check_ids RPAR {List.rev $2 }
|   LPAR error    { raise (Checker.ErrorMsg "<ID> [,<ID>]*\n)") }
    ;




  proc: 
    simple_proc     { $1 }
|   proc PIPE simple_proc { ref (Par($1,$3)) }
|   proc PIPE error { raise (Checker.ErrorMsg "<PROCESS>") }
    ;
    
  simple_proc: 
    ZERO                              
    { ref (Piastnode.Void) }

|   CAPS_ID id_args
    {
     ref (Var($1,$2))
    }

|   NEW res_ids IN simple_proc              
    {
     List.iter 
       (fun id -> 
	 if (Hashtbl.find usage id)=0 then 
	   (
	    print_string "Warning: Unused restricted name ";
	    print_string id;
	    print_newline())
	 else 
	   Hashtbl.remove usage id) 
       $2; 
     ref (New(List.rev $2, $4)) }

|   ID QUESTION LPAR inp_ids RPAR DOT simple_proc     
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     List.iter (fun id -> Hashtbl.remove usage id) $4;
     ref (Act(Input($1, List.rev $4), $7)) }

|   ID QUESTION LPAR inp_ids RPAR     
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     List.iter (fun id -> Hashtbl.remove usage id) $4;
     ref (Act(Input($1, List.rev $4), (ref Piastnode.Void))) }

|   ID BANG LPAR out_ids RPAR DOT simple_proc         
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     ref (Act(Output($1, List.rev $4), $7)) }

|   ID BANG LPAR out_ids RPAR         
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     ref (Act(Output($1, List.rev $4), (ref Piastnode.Void))) }

|   TAU DOT simple_proc
    {
     ref(Act(Tau,$3))}

|   TAU
    {
     ref(Act(Tau,ref Piastnode.Void))}

|   LPARR ID EQ ID RPARR DOT simple_proc
    { 
     (if Hashtbl.mem usage $2 then 
       Hashtbl.replace usage $2 1);
     (if Hashtbl.mem usage $4 then 
       Hashtbl.replace usage $4 1);
      ref (Test($2,$4,$7,Equals)) }

|   LPARR ID NEQ ID RPARR DOT simple_proc
    { 
     (if Hashtbl.mem usage $2 then 
       Hashtbl.replace usage $2 1);
     (if Hashtbl.mem usage $4 then 
       Hashtbl.replace usage $4 1);
      ref (Test($2,$4,$7,Differs)) }

|   SELECT LBR sum RBR
    { $3 }

|   LPAR proc RPAR
    { $2 }
    ;

  act_sum: 
    ID QUESTION LPAR inp_ids RPAR DOT simple_proc 
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     List.iter (fun id -> Hashtbl.remove usage id) $4;
     ref (Act(Input($1, List.rev $4), $7)) }
|   ID QUESTION LPAR inp_ids RPAR     
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     List.iter (fun id -> Hashtbl.remove usage id) $4;
     ref (Act(Input($1, List.rev $4), (ref Piastnode.Void))) }
    ;
|   ID BANG LPAR out_ids RPAR DOT simple_proc         
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     ref (Act(Output($1, List.rev $4), $7)) }
|   ID BANG LPAR out_ids RPAR         
    {
     (if Hashtbl.mem usage $1 then 
       Hashtbl.replace usage $1 1);
     ref (Act(Output($1, List.rev $4), (ref Piastnode.Void))) }
|   TAU DOT simple_proc
    {
     ref(Act(Tau,$3))}
|   TAU
    {
     ref(Act(Tau,ref Piastnode.Void))}
|   LPARR ID EQ ID RPARR DOT simple_proc
    { 
     (if Hashtbl.mem usage $2 then 
       Hashtbl.replace usage $2 1);
     (if Hashtbl.mem usage $4 then 
       Hashtbl.replace usage $4 1);
      ref (Test($2,$4,$7,Equals)) }
|   LPARR ID NEQ ID RPARR DOT simple_proc
    { 
     (if Hashtbl.mem usage $2 then 
       Hashtbl.replace usage $2 1);
     (if Hashtbl.mem usage $4 then 
       Hashtbl.replace usage $4 1);
      ref (Test($2,$4,$7,Differs)) }

  sum:
    act_sum
    { $1 }
|   sum SEMI act_sum
    { ref (Sum($1,$3)) }
    ;

  id_args: 
    { [] }
|   LPAR out_ids RPAR {List.rev $2 }
    ;

  check_ids:
    { [] }
|   ID
    { [$1] }
|   check_ids COMMA ID
    { $3::$1 }
    ;


  inp_ids:
    { [] }
|   ID
    {
     Hashtbl.clear names;
     Hashtbl.add names $1 0;
     Hashtbl.add usage $1 0; 
     [$1]
    }
|   inp_ids COMMA ID
    {
     if Hashtbl.mem names $3 then
       (print_string "Repeated name in input ";
	print_string $3;
	print_newline();
	raise Parsing.Parse_error)
     else
       (Hashtbl.add names $3 0;
	Hashtbl.add usage $3 0; 
	$3::$1)}
    ;
  
  out_ids:
    { [] }
|   ID
    { 
      (if Hashtbl.mem usage $1 then 
	Hashtbl.replace usage $1 1);
      [$1]
    }
|   out_ids COMMA ID
    {
     (if Hashtbl.mem usage $3 then 
       Hashtbl.replace usage $3 1);
       $3::$1 }
    ;

  res_ids:
    ID             
    {
     Hashtbl.clear names;
     Hashtbl.add names $1 0;
     Hashtbl.add usage $1 0;
     [$1] }

|   res_ids COMMA ID     
    {
     if Hashtbl.mem names $3 then
       (print_string "Repeated restricted name ";
	print_string $3;
	print_newline();
	raise Parsing.Parse_error)
     else
       (Hashtbl.add names $3 0;
	Hashtbl.add usage $3 0;
	$3::$1) }
    ;

  def_prop:
    DEFPROP dec_name EQ form { Dec($2, $4) }
|   DEFPROP dec_name EQ error { raise (Checker.ErrorMsg "<FORMULA>") }
|   DEFPROP dec_name error { raise (Checker.ErrorMsg "=\n(") }
|   DEFPROP error { raise (Checker.ErrorMsg "<FORMULA IDENTIFIER>") }
    ;

  dec_name:
    ID LPAR param_ids COMMA props RPAR 
    { ($1,List.rev $3,$5) }
|   ID LPAR param_ids RPAR
    { ($1,List.rev $3,[]) }
|   ID LPAR props RPAR
    { ($1,[],$3) }
|   ID 
    { ($1,[],[]) }
|   ID LPAR error 
    { raise (Checker.ErrorMsg "<ID> [,<ID>]*\n<PROP_ID> [,<PROP_ID>]*\n<ID> [,<ID>]*, <PROP_ID> [,<PROP_ID>]*") }
    ;

  param_ids:
    ID
    {
     Hashtbl.clear names;
     Hashtbl.add names $1 0;
     [$1]
    }
|   param_ids COMMA ID
    {
     if Hashtbl.mem names $3 then
       (print_string "Repeated parameter name ";
	print_string $3;
	print_newline();
	raise Parsing.Parse_error)
     else
       (Hashtbl.add names $3 0;
	$3::$1)}
    ;
  
  props:
    CAPS_ID             
    { 
      Hashtbl.clear names;
      Hashtbl.add names $1 0;
      [$1] 
    }
|   props COMMA CAPS_ID 
    { 
      if Hashtbl.mem names $3 then
	(print_string "Repeated propositional parameter name ";
	 print_string $3;
	 print_newline();
	 raise Parsing.Parse_error)
      else
	(Hashtbl.add names $3 0;
	 List.append $1 [$3])}
    ;

  label_ids:
                 { [] }
|   ID           { [$1] }
|   label_ids COMMA ID { $3::$1 }
    ;

  form: 
    simple_form              { $1 }
|   form PIPE simple_form    { Comp($1,$3) }
|   form DBLPIPE simple_form { Decomp($1,$3) }
|   form IMPLIES simple_form { Implies($1,$3) }
|   form EQUIV simple_form   { Equiv($1,$3) }
|   form AND simple_form     { And($1,$3) }
|   form OR simple_form      { Or($1,$3) }
    ;
  
  simple_form: 
    TRUE
    { True }
|   FALSE
    { False }
|   VOID                              
    { Formastnode.Void }
|   ZERO
    { Formastnode.Void }
|   INT 
    { Formastnode.NumComps($1,Formastnode.EqNum) }
|   LT ZERO
    { Formastnode.NumComps(0,Formastnode.LtNum) }
|   LT INT 
    { Formastnode.NumComps($2,Formastnode.LtNum) }
|   GT ZERO
    { Formastnode.NumComps(0,Formastnode.GtNum) }
|   GT INT
    { Formastnode.NumComps($2,Formastnode.GtNum) }
|   CAPS_ID fixpoint_args
    { PropVar($1,$2) }
|   CAPS_ID
    { PropVar($1,[]) }
|   ID DEQ ID 
    { Eq($1,$3) }
|   ID NEQ ID
    { Neq($1,$3) }
|   ID LPAR args RPAR
    { Abbrev($1, $3) }
|   ID 
    { Abbrev($1, []) }
|   NOT simple_form
    { Not($2) }
|   REVEAL ID DOT simple_form
    { Reveal($2,$4) }
|   REVEALALL ID DOT simple_form
    { RevealAll($2,$4) }
|   HIDDEN ID DOT simple_form
    { Hidden($2,$4) }
|   FRESH ID DOT simple_form
    { Fresh($2,$4) }
|   FREE ID 
    { Free($2) }
|   LT tau GT simple_form
    { MayTau($4) }
|   LPARR tau RPARR simple_form
    { AllTau($4) }
|   LT label GT simple_form
    { MayLab($2,$4) }
|   LPARR label RPARR simple_form
    { AllLab($2,$4) }
|   LT ID BANG GT simple_form
    { MayOutN($2,$5) }
|   LT ID QUESTION GT simple_form
    { MayInpN($2,$5) }
|   LPARR ID BANG RPARR simple_form
    { AllOutN($2,$5) }
|   LPARR ID QUESTION RPARR simple_form
    { AllInpN($2,$5) }
|   LT BANG GT simple_form
    { MayOut($4) }
|   LT QUESTION GT simple_form
    { MayInp($4) }
|   LPARR BANG RPARR simple_form
    { AllOut($4) }
|   LPARR QUESTION RPARR simple_form
    { AllInp($4) }
|   LT ID GT simple_form
    { MayN($2,$4) }
|   LPARR ID RPARR simple_form
    { AllN($2,$4) }
|   LT STAR GT simple_form
    { May($4) }
|   LPARR STAR RPARR simple_form 
    { All($4) }
|   EXISTS ID DOT simple_form
    { Exists($2,$4) }
|   FORALL ID DOT simple_form
    { ForAll($2,$4) }
|   LPAR MAXFIX CAPS_ID fixpoint_args DOT simple_form RPAR fixpoint_args
    { 
        MaxFix($3,$4,$6,$8)
    }
|   MAXFIX CAPS_ID DOT simple_form
    { 
        MaxFix($2,[],$4,[])
    }
|   LPAR MINFIX CAPS_ID fixpoint_args DOT simple_form RPAR fixpoint_args
    {
        MinFix($3,$4,$6,$8)
    }
|   MINFIX CAPS_ID DOT simple_form
    { 
        MinFix($2,[],$4,[])
    }
|   EVENTUALLY simple_form
    { Eventually($2) }
|   ALWAYS simple_form
    { Always($2) }
|   INSIDE simple_form
    { Inside($2) }
|   SHOW_F simple_form
    { Show_f($2) }
|   SHOW_S simple_form
    { Show_s($2) }
|   LPAR form RPAR
    { $2 }
    ;

  fixpoint_args:
    LPAR label_ids RPAR
    { List.rev $2 }
    ;

  label_ids_uscore:
                 { [] }
|   ID           { [$1] }
|   USCORE       { ["_"] }
|   label_ids_uscore COMMA ID { $3::$1 }
|   label_ids_uscore COMMA USCORE { "_"::$1 }
    ;


  label:
    ID QUESTION LPAR label_ids RPAR { InpLab($1,List.rev $4) }
|   ID BANG LPAR label_ids_uscore RPAR { OutLab($1,List.rev $4) }
    ;

  tau:
        { }
|   TAU { }
    ;

  args:
    form            { [$1] }
|   args COMMA form { List.append $1 [$3] }
    ;


cc_simple_proc: 
    END                              
    { CCInact }
|   CAPS_ID id_args
    {
     CCVar($1,$2)
    }
|   CTX ID LBR proc_cc RBR { CCCxt($2,$4) }
|   cc_input { $1 }
|   ID BANG LPAR out_ids RPAR DOT cc_simple_proc { CCAct(CCOutput(Here,$1,List.rev $4),$7) }
|   ID UPC BANG LPAR out_ids RPAR DOT cc_simple_proc { CCAct(CCOutput(Up,$1,List.rev $5),$8) }
|   DEFC ID IMPLIES cc_simple_proc { CCDef($2,$4) }
|   NEW ID DOT ID DEFARROW cc_simple_proc { CCNew($2,$4,$6) }
|   JOIN ID DOT ID DEFARROW cc_simple_proc { CCJoin($2,$4,$6) }
|   SWITCH LBR cc_branches RBR { CCSum(List.rev $3) }
|   THIS LPAR ID RPAR DOT cc_simple_proc { CCThis($3,$6) }
|   IF LPAR ID EQ ID RPAR THEN cc_simple_proc ELSE cc_simple_proc { CCIfThenElse($8,$10) }
|   IF LPAR ID NEQ ID RPAR THEN cc_simple_proc ELSE cc_simple_proc { CCIfThenElse($8,$10) }
|   LPAR proc_cc RPAR { $2 }
;

cc_input:
   ID QUESTION LPAR inp_ids RPAR DOT cc_simple_proc { CCAct(CCInput(Here,$1, List.rev $4),$7) }
|  ID UPC QUESTION LPAR inp_ids RPAR DOT cc_simple_proc { CCAct(CCInput(Up,$1, List.rev $5),$8) }
;

cc_branches:
   cc_input{ [$1] }
|  cc_branches SEMI cc_input { $3::$1 }
;

proc_cc:
    cc_simple_proc     { $1 }
|   proc_cc PIPE cc_simple_proc { CCPar($1,$3) }
|   proc_cc PIPE error { raise (Checker.ErrorMsg "<PROCESS>") }
    ;
    
