structure T = Tokens                (* Abbreviation saves typing *)

(* Type of the line pointer *)
type pos = int
type svalue = T.svalue
type ('a,'b) token = ('a,'b) T.token
type lexresult = (svalue,pos) token
type lexarg = string
type arg = lexarg

(* Initialize line pointer *)
val lin = ref 1;

(* Initialize character position of most recent newline *)
val col = ref 0;
val eolpos = ref 0;

val badCh : string * string * int * int -> unit = fn 
    (fileName,bad,line,col) =>
    TextIO.output(TextIO.stdOut,fileName^"["^Int.toString line
                 ^"."^Int.toString col^"] Invalid character \""
                 ^bad^"\"\n");
(* End of file management *)
val eof = fn fileName => T.EOF (!lin,!col);

%%
%full
%header (functor WhileLexFun(structure Tokens: While_TOKENS));
%arg (fileName:string);
%s WHILE COMMENT;
alpha         = [A-Za-z];
digit         = [0-9];
alhpaNumeric  = [A-Za-z0-9];
sign          = ("+"|"-");
dot           = (".");
whitespace            = [\ \t];
eol           = ("\013\010"|"\010"|"\013");

%%
<INITIAL>{whitespace}* => (lin:=1; eolpos:=0; YYBEGIN WHILE; continue ());

<WHILE>";"                                     => (col:=yypos-(!eolpos); T.SEMICOLON(!lin, !col));
<WHILE>"("{digit}+","{digit}+")"               => (col:=yypos-(!eolpos); T.RATVAL(yytext,!lin, !col));
<WHILE>{sign}{digit}+{dot}{digit}*"("{digit}*")" => (col:=yypos-(!eolpos); T.RATDECFORM(yytext, !lin, !col));
<WHILE>","                                     => (col:=yypos-(!eolpos); T.COMMA(!lin, !col));
<WHILE>"{"                                     => (col:=yypos-(!eolpos); T.LCURLY(!lin, !col));
<WHILE>"}"                                     => (col:=yypos-(!eolpos); T.RCURLY(!lin, !col));
<WHILE>":="                                    => (col:=yypos-(!eolpos); T.ASSIGN(!lin, !col));
<WHILE>"("                                     => (col:=yypos-(!eolpos); T.LPAREN(!lin,!col));
<WHILE>")"                                     => (col:=yypos-(!eolpos); T.RPAREN(!lin,!col));
<WHILE>"||"                                    => (col:=yypos-(!eolpos); T.OR(!lin,!col));
<WHILE>"&&"                                    => (col:=yypos-(!eolpos); T.AND(!lin,!col));
<WHILE>"!"                                     => (col:=yypos-(!eolpos); T.NOT(!lin,!col));
<WHILE>"*"                                     => (col:=yypos-(!eolpos); T.MUL(!lin, !col));
<WHILE>".*."                                   => (col:=yypos-(!eolpos); T.RATMUL(!lin, !col));
<WHILE>"/"                                     => (col:=yypos-(!eolpos); T.DIV(!lin, !col));
<WHILE>"./."                                   => (col:=yypos-(!eolpos); T.RATDIV(!lin, !col));
<WHILE>"%"                                     => (col:=yypos-(!eolpos); T.MOD(!lin, !col));
<WHILE>"+"                                     => (col:=yypos-(!eolpos); T.PLUS(!lin, !col));
<WHILE>".+."                                   => (col:=yypos-(!eolpos); T.RATPLUS(!lin, !col));
<WHILE>"-"                                     => (col:=yypos-(!eolpos); T.MINUS(!lin, !col));
<WHILE>".-."                                   => (col:=yypos-(!eolpos); T.RATMINUS(!lin, !col));
<WHILE>"<"                                     => (col:=yypos-(!eolpos); T.LT(!lin, !col));
<WHILE>">"                                     => (col:=yypos-(!eolpos); T.GT(!lin, !col));
<WHILE>"<="                                    => (col:=yypos-(!eolpos); T.LE(!lin, !col));
<WHILE>">="                                    => (col:=yypos-(!eolpos); T.GE(!lin, !col));
<WHILE>"="                                     => (col:=yypos-(!eolpos); T.EQ(!lin, !col));
<WHILE>"<>"                                    => (col:=yypos-(!eolpos); T.NE(!lin, !col));
<WHILE>"~"                                     => (col:=yypos-(!eolpos); T.NEG(!lin, !col));
<WHILE>"inverse"                               => (col:=yypos-(!eolpos); T.INV(!lin, !col));
<WHILE>"procedure"                             => (col:=yypos-(!eolpos); T.PROCESS(!lin, !col));
<WHILE>"var"                                   => (col:=yypos-(!eolpos); T.VAR(!lin, !col));
<WHILE>"rational"                              => (col:=yypos-(!eolpos); T.RATIONAL(!lin, !col));
<WHILE>"integer"                               => (col:=yypos-(!eolpos); T.INT(!lin, !col));
<WHILE>"boolean"                               => (col:=yypos-(!eolpos); T.BOOL(!lin, !col));
<WHILE>"make_rat"                              => (col:=yypos-(!eolpos); T.MKRAT(!lin, !col));
<WHILE>"rat"                                   => (col:=yypos-(!eolpos); T.RAT(!lin, !col));
<WHILE>"showDecimal"                           => (col:=yypos-(!eolpos); T.SHOWDEC(!lin, !col));
<WHILE>"fromDecimal"                           => (col:=yypos-(!eolpos); T.FROMDEC(!lin, !col));
<WHILE>"toDecimal"                             => (col:=yypos-(!eolpos); T.TODEC(!lin, !col));
<WHILE>"showRat"                               => (col:=yypos-(!eolpos); T.SHOWRAT(!lin, !col));
<WHILE>"read"                                  => (col:=yypos-(!eolpos); T.READ(!lin, !col));
<WHILE>"print"                                 => (col:=yypos-(!eolpos); T.WRITE(!lin, !col));
<WHILE>"call"                                  => (col:=yypos-(!eolpos); T.CALL(!lin, !col));
<WHILE>"if"                                    => (col:=yypos-(!eolpos); T.IF(!lin, !col));
<WHILE>"then"                                  => (col:=yypos-(!eolpos); T.THEN(!lin, !col));
<WHILE>"else"                                  => (col:=yypos-(!eolpos); T.ELSE(!lin, !col));
<WHILE>"fi"                                    => (col:=yypos-(!eolpos); T.FI(!lin, !col));
<WHILE>"while"                                 => (col:=yypos-(!eolpos); T.WHILE(!lin, !col));
<WHILE>"do"                                    => (col:=yypos-(!eolpos); T.DO(!lin, !col));
<WHILE>"od"                                    => (col:=yypos-(!eolpos); T.OD(!lin, !col));
<WHILE>"tt"                                    => (col:=yypos-(!eolpos); T.TT(!lin, !col));
<WHILE>"ff"                                    => (col:=yypos-(!eolpos); T.FF(!lin, !col));
<WHILE>{alpha}{alhpaNumeric}*                  => (col:=yypos-(!eolpos); T.IDENTIFIER(yytext, !lin, !col));
<WHILE>{digit}+                                => (col:=yypos-(!eolpos); T.NUMERAL(BigInt.fromString(yytext), !lin, !col));
<WHILE>{whitespace}*      => (continue ());
<WHILE>{eol}      => (lin:=(!lin)+1; eolpos:=yypos+String.size yytext;               continue ());
<WHILE>.                                       => (col := !col + 1; print("Bad Character: " ^ yytext ^ "\n"); T.BADCH(!lin, !col));