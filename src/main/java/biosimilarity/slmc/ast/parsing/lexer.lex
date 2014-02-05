package biosimilarity.slmc.ast.parsing;
import java_cup.runtime.*;
import biosimilarity.slmc.ast.sr.ParseError;

%% 

%public
%class Lexer
%scanerror ParseError
%cup
%line
%column

%{
  StringBuffer string = new StringBuffer();

  private Symbol symbol(int type) {
    return new Symbol(type, yyline, yycolumn);
  }
  private Symbol symbol(int type, Object value) {
    return new Symbol(type, yyline, yycolumn, value);
  }
  
  public int line() {
    return yyline;
  }
  
  public int column() {
    return yycolumn;
  }
%}

%eofval{
  return symbol(0);
%eofval}

LineTerminator = \r | \n | \r\n
InputCharacter = [^\r\n]
WhiteSpace     = {LineTerminator} | [ \t\f]

/* comments */
Comment = {TraditionalComment} | {EndOfLineComment} | {DocumentationComment}

TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}
DocumentationComment = "/**" {CommentContent} "*"+ "/"
CommentContent       = ( [^*] | \*+ [^/*] )*

Int      = [1-9][0-9]*
LowerId  = [a-z][A-Za-z0-9_]*
CapsId   = [A-Z][A-Za-z0-9_]*
Filename = "\"" ([ !] | [#-~]) "\""

%%
<YYINITIAL> {
  {Comment}       { /* Ignore */; }
  {WhiteSpace}    { /* Ignore */; }
  {Int}           { return symbol(ParserSym.INT, new Integer(yytext())); }
  "true"          { return symbol(ParserSym.TRUE); }
  "false"         { return symbol(ParserSym.FALSE); }
  "void"          { return symbol(ParserSym.VOID); }
  "select"        { return symbol(ParserSym.SELECT); }
  "not"           { return symbol(ParserSym.NOT); }
  "and"           { return symbol(ParserSym.AND); }
  "or"            { return symbol(ParserSym.OR); }
  "reveal"        { return symbol(ParserSym.REVEAL); }
  "revealall"     { return symbol(ParserSym.REVEALALL); }
  "hidden"        { return symbol(ParserSym.HIDDEN); }
  "fresh"         { return symbol(ParserSym.FRESH); }
  "exists"        { return symbol(ParserSym.EXISTS); }
  "forall"        { return symbol(ParserSym.FORALL); }
  "maxfix"        { return symbol(ParserSym.MAXFIX); }
  "minfix"        { return symbol(ParserSym.MINFIX); }
  "eventually"    { return symbol(ParserSym.EVENTUALLY); }
  "always"        { return symbol(ParserSym.ALWAYS); }
  "inside"        { return symbol(ParserSym.INSIDE); }
  "show_fail"     { return symbol(ParserSym.SHOW_F); }
  "show_succeed"  { return symbol(ParserSym.SHOW_S); }
  "tau"           { return symbol(ParserSym.TAU); }
  "defprop"       { return symbol(ParserSym.DEFPROP); }
  "new"           { return symbol(ParserSym.NEW); }
  "in"            { return symbol(ParserSym.IN); }
  "defproc"       { return symbol(ParserSym.DEFPROC); }
  "check"         { return symbol(ParserSym.CHECK); }
  "parameter"     { return symbol(ParserSym.PARAM); }
  "max_threads"   { return symbol(ParserSym.MT); }
  "check_counter" { return symbol(ParserSym.CC); }
  "show_time"     { return symbol(ParserSym.ST); }
  "cd"            { return symbol(ParserSym.CD); }
  "pd"            { return symbol(ParserSym.PD); }
  "trace"         { return symbol(ParserSym.TRACE); } 
  "on"            { return symbol(ParserSym.ON); }
  "off"           { return symbol(ParserSym.OFF); }
  "list"          { return symbol(ParserSym.PRINT); }
  "show"          { return symbol(ParserSym.SHOW); }
  "props"         { return symbol(ParserSym.PROPS); }
  "procs"         { return symbol(ParserSym.PROCS); }
  "clear"         { return symbol(ParserSym.CLEAR); }
  "load"          { return symbol(ParserSym.LOAD); }
  "help"          { return symbol(ParserSym.HELP); }
  "quit"          { return symbol(ParserSym.QUIT); }
  "cc"            { return symbol(ParserSym.CONV); }
  "pi"            { return symbol(ParserSym.PI); }
  "def"           { return symbol(ParserSym.DEFC); }
  "join"          { return symbol(ParserSym.JOIN); }
  "context"       { return symbol(ParserSym.CTX); }
  "switch"        { return symbol(ParserSym.SWITCH); }
  "if"            { return symbol(ParserSym.IF); }
  "then"          { return symbol(ParserSym.THEN); }
  "else"          { return symbol(ParserSym.ELSE); }
  "this"          { return symbol(ParserSym.THIS); }
  "end"           { return symbol(ParserSym.END); }
  {LowerId}       { return symbol(ParserSym.LOWER_ID, yytext()); }
  {CapsId}        { return symbol(ParserSym.CAPS_ID, yytext()); }
  {Filename}      { return symbol(ParserSym.FILENAME, yytext()); }
  "|"             { return symbol(ParserSym.PIPE); }
  "0"             { return symbol(ParserSym.ZERO); }
  "<="            { return symbol(ParserSym.DEFARROW); }
  "<"             { return symbol(ParserSym.LT); }
  ">"             { return symbol(ParserSym.GT); }
  "["             { return symbol(ParserSym.LPARR); }
  "]"             { return symbol(ParserSym.RPARR); }
  "*"             { return symbol(ParserSym.STAR); }
  "!"             { return symbol(ParserSym.BANG); }
  "?"             { return symbol(ParserSym.QUESTION); }
  "."             { return symbol(ParserSym.DOT); }
  "{"             { return symbol(ParserSym.LBR); }
  "}"             { return symbol(ParserSym.RBR); }
  "@"             { return symbol(ParserSym.FREE); }
  "||"            { return symbol(ParserSym.DBLPIPE); }
  "("             { return symbol(ParserSym.LPAR); }
  ")"             { return symbol(ParserSym.RPAR); }
  ","             { return symbol(ParserSym.COMMA); }
  "="             { return symbol(ParserSym.EQ); }
  "=="            { return symbol(ParserSym.DEQ); }
  "!="            { return symbol(ParserSym.NEQ); }
  "=>"            { return symbol(ParserSym.IMPLIES); }
  "<=>"           { return symbol(ParserSym.EQUIV); }
  "|="            { return symbol(ParserSym.SAT); }
  ";"             { return symbol(ParserSym.SEMI); }
  "^"             { return symbol(ParserSym.UPC); }
  "_"             { return symbol(ParserSym.USCORE); }
  .               { throw new ParseError(yytext()); }
}
