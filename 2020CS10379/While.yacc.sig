signature While_TOKENS =
sig
type ('a,'b) token
type svalue
val BADCH:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val NUMERAL: (BigInt.bigint) *  'a * 'a -> (svalue,'a) token
val IDENTIFIER: (string) *  'a * 'a -> (svalue,'a) token
val RATDECFORM: (string) *  'a * 'a -> (svalue,'a) token
val RATVAL: (string) *  'a * 'a -> (svalue,'a) token
val FF:  'a * 'a -> (svalue,'a) token
val TT:  'a * 'a -> (svalue,'a) token
val OD:  'a * 'a -> (svalue,'a) token
val DO:  'a * 'a -> (svalue,'a) token
val WHILE:  'a * 'a -> (svalue,'a) token
val FI:  'a * 'a -> (svalue,'a) token
val ELSE:  'a * 'a -> (svalue,'a) token
val THEN:  'a * 'a -> (svalue,'a) token
val IF:  'a * 'a -> (svalue,'a) token
val CALL:  'a * 'a -> (svalue,'a) token
val WRITE:  'a * 'a -> (svalue,'a) token
val READ:  'a * 'a -> (svalue,'a) token
val SHOWRAT:  'a * 'a -> (svalue,'a) token
val TODEC:  'a * 'a -> (svalue,'a) token
val FROMDEC:  'a * 'a -> (svalue,'a) token
val SHOWDEC:  'a * 'a -> (svalue,'a) token
val RAT:  'a * 'a -> (svalue,'a) token
val MKRAT:  'a * 'a -> (svalue,'a) token
val BOOL:  'a * 'a -> (svalue,'a) token
val INT:  'a * 'a -> (svalue,'a) token
val RATIONAL:  'a * 'a -> (svalue,'a) token
val VAR:  'a * 'a -> (svalue,'a) token
val PROCESS:  'a * 'a -> (svalue,'a) token
val INV:  'a * 'a -> (svalue,'a) token
val NEG:  'a * 'a -> (svalue,'a) token
val NE:  'a * 'a -> (svalue,'a) token
val EQ:  'a * 'a -> (svalue,'a) token
val GE:  'a * 'a -> (svalue,'a) token
val LE:  'a * 'a -> (svalue,'a) token
val GT:  'a * 'a -> (svalue,'a) token
val LT:  'a * 'a -> (svalue,'a) token
val RATMINUS:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val RATPLUS:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val MOD:  'a * 'a -> (svalue,'a) token
val RATDIV:  'a * 'a -> (svalue,'a) token
val DIV:  'a * 'a -> (svalue,'a) token
val RATMUL:  'a * 'a -> (svalue,'a) token
val MUL:  'a * 'a -> (svalue,'a) token
val NOT:  'a * 'a -> (svalue,'a) token
val AND:  'a * 'a -> (svalue,'a) token
val OR:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val ASSIGN:  'a * 'a -> (svalue,'a) token
val RCURLY:  'a * 'a -> (svalue,'a) token
val LCURLY:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
end
signature While_LRVALS=
sig
structure Tokens : While_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
