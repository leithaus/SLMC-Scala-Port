(*** Model checker's main module ***)

open Checker
open Mcmenu

(* Auxiliar function that finds the lines surrounding a syntax error *)

let error_position pos filename =
  let c = open_in filename in
  let i = ref 0 in
  let line = ref 1 in
  let column = ref 0 in
  let queue = ref [""] in
  let not_found = ref true in
  (try
    while !not_found do
      let s = input_line c in
      if !i + (String.length s)+1 > pos then
	try
	  not_found := false;
	  column := pos - !i;
	  queue := (List.hd !queue)::(s::[input_line c])
	with End_of_file -> queue := (List.hd !queue)::(s::[""])
      else
	(incr line; i := !i + (String.length s)+1; queue := [s])
    done
  with End_of_file -> queue := (List.hd !queue)::["";""]);
  (!queue, !line, !column)

(* Auxiliar print function *)

let rec print_strings sl =
  match sl with
    [] -> print_string ""
  | hd::tl -> print_string (hd^"\n") ; print_strings tl

(* Main procedure *)

let main () = 
  let not_done = ref true in
  let file = ref false in
  let queue = ref [Lexing.from_channel (stdin)] in
  let file_queue = ref [] in
  let aux_queue = ref [] in
  let files = Hashtbl.create 10 in
  print_string "\n*** SPATIAL LOGIC MODEL CHECKER ***\n";
  print_string   "***        v2.01-Nov-09         ***\n\n";
  flush stdout;
  while !not_done do
    try
      if not (!file) then
	(print_string "> "; flush stdout);
      let option = Mcparser.main Mclexer.token (List.hd !queue) in
      flush stdout;
      match option with
	Defproc(proc_dec)  -> install_proc proc_dec
      | Defprop(prop_dec)  -> install_prop prop_dec
      | Check(chk_args)    -> top_check chk_args
      | DefMaxThreads(i)   -> def_maxthreads i
      | PrintMaxThreads    -> show_maxthreads(); print_newline()
      | DefCheckCounter(b) -> def_checkcounter b
      | PrintCheckCounter  -> checkcounter_val(); print_newline()
      | DefShowTime(b)     -> def_showtime b
      | PrintShowTime      -> showtime_val(); print_newline()
      | ListParams         -> print_string "\n- Listing parameters -\n\nmax_threads\nshow_time\ncheck_counter\n\n"
      | DefTrace(b)        -> trace b
      | PrintTrace         -> trace_val(); print_newline()
      | CD(dirname)        -> Sys.chdir (String.sub dirname 1 ((String.length dirname)-2))
      | PD                 -> print_string "\n- Current directory -\n\n"; print_string (Sys.getcwd()^"\n\n")
      | Load(filename)     -> 
	  let fid = String.sub filename 1 ((String.length filename)-2) in
	  if not (Hashtbl.mem files fid) then
	    (let fic = open_in fid in
	    file_queue := (fic)::!file_queue;
	    queue := (Lexing.from_channel (fic))::!queue;
	    aux_queue := (fid)::!aux_queue;
	    Hashtbl.add files fid 0;
	    if not !file then
	      file := true)
      | Clear              -> clear()
      | ShowProc(proc_id)  -> show_proc proc_id
      | ShowProp(prop_id)  -> show_prop prop_id
      | PrintProcs         -> print_string "\n- Listing processes -\n\n"; print_procs(); print_newline()
      | PrintProps         -> print_string "\n- Listing properties -\n\n";print_props(); print_newline()
      | Help               -> 
	  print_string "\n- Listing commands -\n\n";
          print_string "defproc ID[(n1,...)] = <process> (and ID[(n1,...)] = <process>)*;";
	  print_string "\ndefprop id[(n1,...,P1,...)] = <formula>;";
	  print_string "\ncheck <process id> [(n1,...)] |= <formula>;";
	  print_string "\nparameter [<parameter id> [new_value]];";
	  print_string "\nlist [procs | props];\nshow [id | ID];\nload \"<filename>\";";
	  print_string "\ncd \"<pathname>\";\npd;"; 
	  print_string "\ntrace [on | off];\nclear;\nhelp;\nquit;\n\n"
      | Continue           -> print_newline()
      | Done               ->
	  if !file then 
	    (queue := List.tl !queue;
	     close_in (List.hd !file_queue);
	     file_queue := List.tl !file_queue;
	     aux_queue := List.tl !aux_queue;
	     if List.length !queue = 1 then
	       (Hashtbl.clear files;
		file := false))
	  else 
	    not_done := false
    with  
      Not_found ->
	print_string "Undeclared...\n";
	flush stdout 
    | Checker.Undeclared(x) ->
	print_string ("\n<<< Unknown identifier: "^x^" >>>\n\n");
	flush stdout 
    | Checker.Wrong_args(x) ->
	print_string ("\n<<< Incorrect usage of "^x^" >>>\n\n");
	flush stdout 
    | Checker.UnguardedRec(x) ->
	print_string ("\n<<< Unguarded recursion found in process "^x^" >>>\n\n");
	flush stdout
    | Checker.MaxThreads ->
	print_string ("\n<<< Unable to perform check - topped out on number of threads >>>\n\n");
	flush stdout
    | Equations.WrongNumArgs(x) ->
	print_string ("\n<<< Incorrect usage of "^x^" >>>\n\n");
	flush stdout 
    | Equations.UndeclaredId(x) ->
	print_string ("\n<<< Unknown identifier: "^x^" >>>\n\n");
	flush stdout
    | Piastnode.Ill_formed_ast ->
	print_string "\n<<< Ill formed process! >>>\n\n";
	flush stdout 
    | Formastnode.Ill_formed_form ->
	print_string "\n<<< Ill formed formula! >>>\n\n";
	flush stdout 
    | Sys_error(x) ->
	print_string ("\n<<< IO error! "^x^" >>>\n\n"); 
	flush stdout 
    | Checker.ErrorMsg(x) ->
	if !file then 
          (let (strs,line,col) = error_position 
	      (Lexing.lexeme_start (List.hd !queue)) (List.hd !aux_queue) in
	  print_string "\n<<< ";
	  print_string ("Line "^(string_of_int line));
	  print_string (" column "^(string_of_int col)^"!");
	  print_string " >>>";
	  print_string "\n\nContext:\n***************\n";
	  print_strings strs;
	  print_string ("***************\n\n");
	  queue := List.tl !queue;
	  close_in (List.hd !file_queue);
	  file_queue := List.tl !file_queue;
	  aux_queue := List.tl !aux_queue;
	  if List.length !queue = 1 then
	    (Hashtbl.clear files;
	     file := false))
	else
	  (print_string "\n<<< Syntax error! >>>\n\n";
	   queue := [Lexing.from_channel stdin]);
	print_string ("Expecting:\n"^x^"\n\n");
	flush stdout;
    | Parsing.Parse_error ->
	if !file then 
          (let (strs,line,col) = error_position 
	      (Lexing.lexeme_start (List.hd !queue)) (List.hd !aux_queue) in
	  print_string "\n<<< ";
	  print_string ("Syntax error in line "^(string_of_int line));
	  print_string (" column "^(string_of_int col)^"!");
	  print_string " >>>";
	  print_string "\n\nContext:\n***************\n";
	  print_strings strs;
	  print_string ("***************\n\n");
	  flush stdout;
	  queue := List.tl !queue;
	  close_in (List.hd !file_queue);
	  file_queue := List.tl !file_queue;
	  aux_queue := List.tl !aux_queue;
	  if List.length !queue = 1 then
	    (Hashtbl.clear files;
	     file := false))
	else
	  (print_string "\n<<< Syntax error! >>>\n\n";
	   flush stdout;
	   queue := [Lexing.from_channel stdin])
    | Failure x ->
	print_string "Failure...\n"; 
	flush stdout;
	file := false;
	Hashtbl.clear files;
	queue := [Lexing.from_channel stdin];
	aux_queue := [];
	List.iter (fun fic -> close_in fic) !file_queue
  done;
  print_string "\nExiting...\n"; exit 0;;

main();;

(***)
