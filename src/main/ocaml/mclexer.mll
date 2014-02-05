(*** Lexer Module ***)
{
 open Mcparser
}

  rule token = parse
  [' ' '\t' '\n' '\r']     { token lexbuf }
| "/*"                     { comment lexbuf }
| ['1'-'9'] (['0'-'9']*)
    { INT(int_of_string (Lexing.lexeme lexbuf)) }
| ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_'] *
    { 
      let id = Lexing.lexeme lexbuf in		
      match id with 
	      "true" -> TRUE
      | "false" -> FALSE
      | "void" -> VOID
      | "select" -> SELECT
      | "not" -> NOT
      | "and" -> AND
      | "or" -> OR
      | "reveal" -> REVEAL
      | "revealall" -> REVEALALL
      | "hidden" -> HIDDEN
      | "fresh" -> FRESH
      | "exists" -> EXISTS
      | "forall" -> FORALL
      | "maxfix" -> MAXFIX
      | "minfix" -> MINFIX
      | "eventually" -> EVENTUALLY
      | "always" -> ALWAYS
      | "inside" -> INSIDE
      | "show_fail" -> SHOW_F
      | "show_succeed" -> SHOW_S
      | "tau" -> TAU
      | "defprop" -> DEFPROP
      | "new" -> NEW 
      | "rec" -> REC 
      | "in" -> IN
      | "defproc" -> DEFPROC
      | "check" -> CHECK
      | "parameter" -> PARAM
      | "max_threads" -> MT
      | "check_counter" -> CC
      | "show_time" -> ST
      | "cd" -> CD
      | "pd" -> PD
      | "trace" -> TRACE 
      | "on" -> ON
      | "off" -> OFF
      | "list" -> PRINT 
      | "show" -> SHOW
      | "props" -> PROPS
      | "procs" -> PROCS
      | "clear" -> CLEAR
      | "load" -> LOAD
      | "help" -> HELP
      | "quit" -> QUIT
      | "cc" -> CONV
      | "pi" -> PI
      | "def" -> DEFC
      | "join" -> JOIN
      | "context" -> CTX
      | "switch" -> SWITCH
      | "if" -> IF
      | "then" -> THEN
      | "else" -> ELSE
      | "this" -> THIS
      | "end" -> END
      | _ -> ID(id) 
    }
| ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_'] * 
    { CAPS_ID(Lexing.lexeme lexbuf) }
| '"' [' ' '!' '#'-'~']* '"'
    { FILENAME(Lexing.lexeme lexbuf) }
| '|'            { PIPE }
| '0'            { ZERO }
| "<="           { DEFARROW }
| '<'            { LT }
| '>'            { GT }
| '['            { LPARR }
| ']'            { RPARR }
| '*'            { STAR }
| '!'            { BANG }
| '?'            { QUESTION }
| '.'            { DOT }
| '{'            { LBR }
| '}'            { RBR }
| '@'            { FREE }
| "||"           { DBLPIPE }
| '('            { LPAR }
| ')'            { RPAR }
| ','            { COMMA }
| '='            { EQ }
| "=="           { DEQ }
| "!="           { NEQ }
| "=>"           { IMPLIES }
| "<=>"          { EQUIV }
| "|="           { SAT }
| ';'            { SEMI }
| "^"            { UPC }
| "_"            { USCORE }
| eof            { EOF }
| _              { raise Parsing.Parse_error }

and comment = parse
  '*'* "*/"                       { token lexbuf }
| ['\t' '\n' '\r']                { comment lexbuf }
| [' '-')' '+'-'.' '0'-'~']*      { comment lexbuf }
| '*'+ [' '-')' '+'-'.' '0'-'~']+ { comment lexbuf }
| '/'+                            { comment lexbuf }
| _                               { raise Parsing.Parse_error }
