functor WhileLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : While_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\214\000\007\000\214\000\008\000\233\000\009\000\233\000\
\\011\000\214\000\012\000\219\000\013\000\214\000\014\000\219\000\
\\015\000\214\000\016\000\214\000\017\000\219\000\018\000\214\000\
\\019\000\219\000\020\000\214\000\021\000\214\000\022\000\214\000\
\\023\000\214\000\024\000\214\000\025\000\214\000\043\000\233\000\
\\047\000\233\000\000\000\
\\001\000\001\000\214\000\007\000\214\000\011\000\214\000\012\000\219\000\
\\013\000\214\000\014\000\219\000\015\000\214\000\016\000\214\000\
\\017\000\219\000\018\000\214\000\019\000\219\000\020\000\214\000\
\\021\000\214\000\022\000\214\000\023\000\214\000\024\000\214\000\
\\025\000\214\000\000\000\
\\001\000\001\000\227\000\007\000\227\000\008\000\227\000\009\000\076\000\
\\024\000\227\000\025\000\227\000\043\000\227\000\047\000\227\000\000\000\
\\001\000\001\000\229\000\007\000\229\000\008\000\229\000\009\000\229\000\
\\024\000\229\000\025\000\229\000\043\000\229\000\047\000\229\000\000\000\
\\001\000\001\000\236\000\007\000\236\000\008\000\230\000\009\000\230\000\
\\024\000\230\000\025\000\230\000\043\000\236\000\047\000\236\000\000\000\
\\001\000\001\000\021\000\000\000\
\\001\000\001\000\032\000\000\000\
\\001\000\001\000\034\000\000\000\
\\001\000\001\000\037\000\000\000\
\\001\000\001\000\071\000\000\000\
\\001\000\003\000\014\000\000\000\
\\001\000\004\000\038\000\000\000\
\\001\000\005\000\039\000\000\000\
\\001\000\006\000\060\000\010\000\059\000\016\000\058\000\026\000\057\000\
\\033\000\056\000\036\000\055\000\049\000\054\000\050\000\053\000\
\\051\000\052\000\053\000\017\000\054\000\051\000\000\000\
\\001\000\006\000\063\000\053\000\017\000\000\000\
\\001\000\006\000\067\000\016\000\058\000\026\000\057\000\033\000\056\000\
\\036\000\055\000\051\000\052\000\053\000\017\000\054\000\051\000\000\000\
\\001\000\006\000\069\000\053\000\017\000\000\000\
\\001\000\006\000\104\000\052\000\103\000\000\000\
\\001\000\006\000\107\000\051\000\106\000\000\000\
\\001\000\006\000\127\000\016\000\126\000\026\000\125\000\033\000\056\000\
\\036\000\055\000\051\000\052\000\053\000\017\000\000\000\
\\001\000\006\000\133\000\016\000\132\000\026\000\131\000\053\000\017\000\
\\054\000\051\000\000\000\
\\001\000\007\000\158\000\008\000\085\000\024\000\084\000\025\000\083\000\000\000\
\\001\000\007\000\159\000\017\000\093\000\019\000\092\000\000\000\
\\001\000\007\000\159\000\017\000\093\000\019\000\092\000\020\000\091\000\
\\021\000\090\000\022\000\089\000\023\000\088\000\024\000\087\000\
\\025\000\086\000\000\000\
\\001\000\007\000\160\000\016\000\101\000\018\000\100\000\000\000\
\\001\000\007\000\160\000\016\000\101\000\018\000\100\000\020\000\099\000\
\\021\000\098\000\022\000\097\000\023\000\096\000\024\000\095\000\
\\025\000\094\000\000\000\
\\001\000\007\000\162\000\000\000\
\\001\000\007\000\163\000\000\000\
\\001\000\007\000\165\000\000\000\
\\001\000\007\000\166\000\000\000\
\\001\000\008\000\085\000\024\000\084\000\025\000\083\000\000\000\
\\001\000\008\000\085\000\024\000\084\000\025\000\083\000\043\000\117\000\000\000\
\\001\000\008\000\085\000\024\000\084\000\025\000\083\000\047\000\082\000\000\000\
\\001\000\016\000\101\000\018\000\100\000\020\000\099\000\021\000\098\000\
\\022\000\097\000\023\000\096\000\024\000\095\000\025\000\094\000\000\000\
\\001\000\017\000\093\000\019\000\092\000\020\000\091\000\021\000\090\000\
\\022\000\089\000\023\000\088\000\024\000\087\000\025\000\086\000\000\000\
\\001\000\044\000\167\000\000\000\
\\001\000\045\000\169\000\000\000\
\\001\000\048\000\164\000\000\000\
\\001\000\051\000\106\000\000\000\
\\001\000\052\000\103\000\000\000\
\\001\000\053\000\017\000\000\000\
\\001\000\055\000\000\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\030\000\007\000\000\000\
\\177\000\000\000\
\\178\000\031\000\009\000\000\000\
\\179\000\000\000\
\\180\000\032\000\019\000\000\000\
\\181\000\000\000\
\\182\000\028\000\012\000\000\000\
\\183\000\000\000\
\\184\000\000\000\
\\185\000\002\000\031\000\000\000\
\\186\000\000\000\
\\187\000\000\000\
\\188\000\039\000\030\000\040\000\029\000\041\000\028\000\042\000\027\000\
\\046\000\026\000\053\000\017\000\000\000\
\\189\000\017\000\093\000\019\000\092\000\020\000\091\000\021\000\090\000\
\\022\000\089\000\023\000\088\000\024\000\087\000\025\000\086\000\000\000\
\\190\000\008\000\085\000\024\000\084\000\025\000\083\000\000\000\
\\191\000\016\000\101\000\018\000\100\000\020\000\099\000\021\000\098\000\
\\022\000\097\000\023\000\096\000\024\000\095\000\025\000\094\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\016\000\101\000\018\000\100\000\000\000\
\\197\000\017\000\093\000\019\000\092\000\000\000\
\\198\000\000\000\
\\199\000\000\000\
\\200\000\012\000\078\000\014\000\077\000\000\000\
\\201\000\012\000\078\000\014\000\077\000\000\000\
\\202\000\012\000\078\000\014\000\077\000\000\000\
\\203\000\011\000\081\000\013\000\080\000\015\000\079\000\000\000\
\\204\000\011\000\081\000\013\000\080\000\015\000\079\000\000\000\
\\205\000\011\000\081\000\013\000\080\000\015\000\079\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\000\000\
\\213\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\000\000\
\\217\000\000\000\
\\218\000\000\000\
\\219\000\000\000\
\\220\000\000\000\
\\221\000\000\000\
\\222\000\000\000\
\\223\000\000\000\
\\224\000\000\000\
\\225\000\000\000\
\\226\000\000\000\
\\228\000\009\000\076\000\000\000\
\\230\000\000\000\
\\231\000\000\000\
\\232\000\000\000\
\\234\000\000\000\
\\235\000\000\000\
\\237\000\016\000\101\000\018\000\100\000\000\000\
\\238\000\016\000\101\000\018\000\100\000\000\000\
\\239\000\016\000\101\000\018\000\100\000\000\000\
\\240\000\016\000\101\000\018\000\100\000\000\000\
\\241\000\016\000\101\000\018\000\100\000\000\000\
\\242\000\016\000\101\000\018\000\100\000\000\000\
\\243\000\017\000\093\000\019\000\092\000\000\000\
\\244\000\017\000\093\000\019\000\092\000\000\000\
\\245\000\017\000\093\000\019\000\092\000\000\000\
\\246\000\017\000\093\000\019\000\092\000\000\000\
\\247\000\017\000\093\000\019\000\092\000\000\000\
\\248\000\017\000\093\000\019\000\092\000\000\000\
\\249\000\008\000\085\000\024\000\084\000\025\000\083\000\000\000\
\\250\000\008\000\085\000\024\000\084\000\025\000\083\000\000\000\
\\251\000\000\000\
\\252\000\000\000\
\\253\000\000\000\
\"
val actionRowNumbers =
"\047\000\049\000\053\000\010\000\
\\042\000\040\000\051\000\040\000\
\\005\000\044\000\040\000\043\000\
\\059\000\056\000\006\000\118\000\
\\045\000\040\000\007\000\053\000\
\\047\000\008\000\011\000\012\000\
\\013\000\013\000\014\000\015\000\
\\016\000\040\000\046\000\009\000\
\\048\000\052\000\054\000\059\000\
\\057\000\013\000\102\000\099\000\
\\098\000\079\000\083\000\073\000\
\\076\000\032\000\034\000\033\000\
\\000\000\084\000\089\000\101\000\
\\100\000\017\000\018\000\015\000\
\\015\000\013\000\013\000\031\000\
\\063\000\040\000\068\000\067\000\
\\001\000\015\000\065\000\040\000\
\\055\000\050\000\058\000\061\000\
\\060\000\062\000\013\000\019\000\
\\019\000\020\000\020\000\020\000\
\\010\000\013\000\013\000\013\000\
\\019\000\019\000\019\000\019\000\
\\019\000\019\000\019\000\019\000\
\\020\000\020\000\020\000\020\000\
\\020\000\020\000\020\000\020\000\
\\094\000\119\000\039\000\096\000\
\\120\000\038\000\092\000\087\000\
\\093\000\088\000\004\000\030\000\
\\021\000\023\000\025\000\010\000\
\\026\000\022\000\024\000\027\000\
\\003\000\078\000\090\000\019\000\
\\019\000\019\000\077\000\082\000\
\\085\000\020\000\020\000\020\000\
\\081\000\080\000\037\000\117\000\
\\116\000\002\000\113\000\112\000\
\\115\000\111\000\114\000\110\000\
\\072\000\071\000\107\000\106\000\
\\109\000\105\000\108\000\104\000\
\\075\000\074\000\028\000\029\000\
\\103\000\091\000\086\000\035\000\
\\064\000\066\000\070\000\095\000\
\\097\000\010\000\036\000\069\000\
\\041\000"
val gotoT =
"\
\\001\000\168\000\002\000\004\000\003\000\003\000\004\000\002\000\
\\006\000\001\000\000\000\
\\007\000\006\000\000\000\
\\005\000\009\000\009\000\008\000\000\000\
\\010\000\011\000\000\000\
\\000\000\
\\011\000\014\000\012\000\013\000\000\000\
\\008\000\016\000\000\000\
\\011\000\018\000\012\000\013\000\000\000\
\\000\000\
\\000\000\
\\012\000\020\000\000\000\
\\000\000\
\\012\000\023\000\013\000\022\000\014\000\021\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\031\000\012\000\013\000\000\000\
\\000\000\
\\005\000\033\000\009\000\008\000\000\000\
\\002\000\034\000\003\000\003\000\004\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\045\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\059\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\012\000\060\000\000\000\
\\012\000\064\000\015\000\063\000\016\000\062\000\018\000\044\000\
\\019\000\043\000\020\000\042\000\021\000\041\000\000\000\
\\012\000\066\000\000\000\
\\011\000\068\000\012\000\013\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\023\000\013\000\070\000\014\000\021\000\000\000\
\\000\000\
\\012\000\048\000\015\000\073\000\016\000\072\000\017\000\071\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\025\000\100\000\000\000\
\\026\000\103\000\000\000\
\\012\000\064\000\020\000\107\000\021\000\106\000\000\000\
\\012\000\064\000\020\000\109\000\021\000\108\000\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\111\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\110\000\024\000\038\000\000\000\
\\012\000\048\000\015\000\114\000\016\000\113\000\017\000\112\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\000\000\
\\000\000\
\\012\000\116\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\064\000\015\000\118\000\016\000\117\000\018\000\044\000\
\\019\000\043\000\020\000\042\000\021\000\041\000\000\000\
\\000\000\
\\012\000\119\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\111\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\120\000\024\000\038\000\000\000\
\\012\000\122\000\021\000\121\000\000\000\
\\012\000\122\000\021\000\126\000\000\000\
\\012\000\128\000\020\000\127\000\000\000\
\\012\000\128\000\020\000\132\000\000\000\
\\012\000\128\000\020\000\133\000\000\000\
\\010\000\134\000\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\135\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\136\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\040\000\023\000\039\000\024\000\038\000\000\000\
\\012\000\048\000\015\000\047\000\016\000\046\000\017\000\111\000\
\\018\000\044\000\019\000\043\000\020\000\042\000\021\000\041\000\
\\022\000\137\000\023\000\039\000\024\000\038\000\000\000\
\\012\000\122\000\016\000\138\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\016\000\139\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\016\000\140\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\016\000\141\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\016\000\142\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\016\000\143\000\019\000\043\000\021\000\041\000\000\000\
\\012\000\122\000\019\000\144\000\021\000\041\000\000\000\
\\012\000\122\000\019\000\145\000\021\000\041\000\000\000\
\\012\000\128\000\015\000\146\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\015\000\147\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\015\000\148\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\015\000\149\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\015\000\150\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\015\000\151\000\018\000\044\000\020\000\042\000\000\000\
\\012\000\128\000\018\000\152\000\020\000\042\000\000\000\
\\012\000\128\000\018\000\153\000\020\000\042\000\000\000\
\\000\000\
\\000\000\
\\025\000\154\000\000\000\
\\000\000\
\\000\000\
\\026\000\155\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\159\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\122\000\021\000\106\000\000\000\
\\012\000\122\000\021\000\108\000\000\000\
\\012\000\122\000\016\000\117\000\019\000\043\000\021\000\041\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\128\000\020\000\107\000\000\000\
\\012\000\128\000\020\000\109\000\000\000\
\\012\000\128\000\015\000\118\000\018\000\044\000\020\000\042\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\166\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 169
val numrules = 83
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = string
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | NUMERAL of unit ->  (BigInt.bigint)
 | IDENTIFIER of unit ->  (string) | RATDECFORM of unit ->  (string)
 | RATVAL of unit ->  (string) | RationalForm of unit ->  (AST.AST)
 | DecimalForm of unit ->  (AST.AST)
 | Comparison of unit ->  (AST.AST) | BoolFactor of unit ->  (AST.AST)
 | BoolTerm of unit ->  (AST.AST) | RatFactor of unit ->  (AST.AST)
 | IntFactor of unit ->  (AST.AST) | RatTerm of unit ->  (AST.AST)
 | IntTerm of unit ->  (AST.AST)
 | BoolExpression of unit ->  (AST.AST)
 | RatExpression of unit ->  (AST.AST)
 | IntExpression of unit ->  (AST.AST) | Command of unit ->  (AST.AST)
 | Commands of unit ->  (AST.AST list)
 | Variable of unit ->  (AST.AST)
 | VariableList of unit ->  (AST.AST list)
 | CommandSeq of unit ->  (AST.AST list)
 | ProcDefs of unit ->  (AST.AST)
 | BoolVarDecls of unit ->  (AST.AST list)
 | IntVarDecls of unit ->  (AST.AST list)
 | RatVarDecls of unit ->  (AST.AST list)
 | ProcDecls of unit ->  (AST.AST list)
 | VarDecls of unit ->  (AST.AST list*AST.AST list*AST.AST list)
 | DeclarationSeq of unit ->  ( ( AST.AST list *  AST.AST list * AST.AST list ) *AST.AST list)
 | Block of unit ->  ( ( (AST.AST list *  AST.AST list * AST.AST list) * AST.AST list ) *AST.AST list)
 | Program of unit ->  (AST.AST)
end
type svalue = MlyValue.svalue
type result = AST.AST
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 54) => true | _ => false
val showTerminal =
fn (T 0) => "SEMICOLON"
  | (T 1) => "COMMA"
  | (T 2) => "LCURLY"
  | (T 3) => "RCURLY"
  | (T 4) => "ASSIGN"
  | (T 5) => "LPAREN"
  | (T 6) => "RPAREN"
  | (T 7) => "OR"
  | (T 8) => "AND"
  | (T 9) => "NOT"
  | (T 10) => "MUL"
  | (T 11) => "RATMUL"
  | (T 12) => "DIV"
  | (T 13) => "RATDIV"
  | (T 14) => "MOD"
  | (T 15) => "PLUS"
  | (T 16) => "RATPLUS"
  | (T 17) => "MINUS"
  | (T 18) => "RATMINUS"
  | (T 19) => "LT"
  | (T 20) => "GT"
  | (T 21) => "LE"
  | (T 22) => "GE"
  | (T 23) => "EQ"
  | (T 24) => "NE"
  | (T 25) => "NEG"
  | (T 26) => "INV"
  | (T 27) => "PROCESS"
  | (T 28) => "VAR"
  | (T 29) => "RATIONAL"
  | (T 30) => "INT"
  | (T 31) => "BOOL"
  | (T 32) => "MKRAT"
  | (T 33) => "RAT"
  | (T 34) => "SHOWDEC"
  | (T 35) => "FROMDEC"
  | (T 36) => "TODEC"
  | (T 37) => "SHOWRAT"
  | (T 38) => "READ"
  | (T 39) => "WRITE"
  | (T 40) => "CALL"
  | (T 41) => "IF"
  | (T 42) => "THEN"
  | (T 43) => "ELSE"
  | (T 44) => "FI"
  | (T 45) => "WHILE"
  | (T 46) => "DO"
  | (T 47) => "OD"
  | (T 48) => "TT"
  | (T 49) => "FF"
  | (T 50) => "RATVAL"
  | (T 51) => "RATDECFORM"
  | (T 52) => "IDENTIFIER"
  | (T 53) => "NUMERAL"
  | (T 54) => "EOF"
  | (T 55) => "BADCH"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 55) $$ (T 54) $$ (T 49) $$ (T 48) $$ (T 47) $$ (T 46) $$ (T 45)
 $$ (T 44) $$ (T 43) $$ (T 42) $$ (T 41) $$ (T 40) $$ (T 39) $$ (T 38)
 $$ (T 37) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31)
 $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24)
 $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17)
 $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10)
 $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 
2) $$ (T 1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (fileName):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.Block Block1, Block1left, Block1right)) :: 
rest671)) => let val  result = MlyValue.Program (fn _ => let val  (
Block as Block1) = Block1 ()
 in ((AST.Procdeff(AST.Variable("_main"),Block)))
end)
 in ( LrTable.NT 0, ( result, Block1left, Block1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.CommandSeq CommandSeq1, _, CommandSeq1right)
) :: ( _, ( MlyValue.DeclarationSeq DeclarationSeq1, 
DeclarationSeq1left, _)) :: rest671)) => let val  result = 
MlyValue.Block (fn _ => let val  (DeclarationSeq as DeclarationSeq1) =
 DeclarationSeq1 ()
 val  (CommandSeq as CommandSeq1) = CommandSeq1 ()
 in ((DeclarationSeq, CommandSeq))
end)
 in ( LrTable.NT 1, ( result, DeclarationSeq1left, CommandSeq1right), 
rest671)
end
|  ( 2, ( ( _, ( MlyValue.ProcDecls ProcDecls1, _, ProcDecls1right))
 :: ( _, ( MlyValue.VarDecls VarDecls1, VarDecls1left, _)) :: rest671)
) => let val  result = MlyValue.DeclarationSeq (fn _ => let val  (
VarDecls as VarDecls1) = VarDecls1 ()
 val  (ProcDecls as ProcDecls1) = ProcDecls1 ()
 in ((VarDecls, ProcDecls))
end)
 in ( LrTable.NT 2, ( result, VarDecls1left, ProcDecls1right), rest671
)
end
|  ( 3, ( ( _, ( MlyValue.BoolVarDecls BoolVarDecls1, _, 
BoolVarDecls1right)) :: ( _, ( MlyValue.IntVarDecls IntVarDecls1, _, _
)) :: ( _, ( MlyValue.RatVarDecls RatVarDecls1, RatVarDecls1left, _))
 :: rest671)) => let val  result = MlyValue.VarDecls (fn _ => let val 
 (RatVarDecls as RatVarDecls1) = RatVarDecls1 ()
 val  (IntVarDecls as IntVarDecls1) = IntVarDecls1 ()
 val  (BoolVarDecls as BoolVarDecls1) = BoolVarDecls1 ()
 in ((RatVarDecls, IntVarDecls, BoolVarDecls))
end)
 in ( LrTable.NT 3, ( result, RatVarDecls1left, BoolVarDecls1right), 
rest671)
end
|  ( 4, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( 
MlyValue.VariableList VariableList1, _, _)) :: ( _, ( _, RATIONAL1left
, _)) :: rest671)) => let val  result = MlyValue.RatVarDecls (fn _ =>
 let val  (VariableList as VariableList1) = VariableList1 ()
 in ((VariableList))
end)
 in ( LrTable.NT 5, ( result, RATIONAL1left, SEMICOLON1right), rest671
)
end
|  ( 5, ( rest671)) => let val  result = MlyValue.RatVarDecls (fn _ =>
 ([]))
 in ( LrTable.NT 5, ( result, defaultPos, defaultPos), rest671)
end
|  ( 6, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( 
MlyValue.VariableList VariableList1, _, _)) :: ( _, ( _, INT1left, _))
 :: rest671)) => let val  result = MlyValue.IntVarDecls (fn _ => let
 val  (VariableList as VariableList1) = VariableList1 ()
 in ((VariableList))
end)
 in ( LrTable.NT 6, ( result, INT1left, SEMICOLON1right), rest671)
end
|  ( 7, ( rest671)) => let val  result = MlyValue.IntVarDecls (fn _ =>
 ([]))
 in ( LrTable.NT 6, ( result, defaultPos, defaultPos), rest671)
end
|  ( 8, ( ( _, ( _, _, SEMICOLON1right)) :: ( _, ( 
MlyValue.VariableList VariableList1, _, _)) :: ( _, ( _, BOOL1left, _)
) :: rest671)) => let val  result = MlyValue.BoolVarDecls (fn _ => let
 val  (VariableList as VariableList1) = VariableList1 ()
 in ((VariableList))
end)
 in ( LrTable.NT 7, ( result, BOOL1left, SEMICOLON1right), rest671)

end
|  ( 9, ( rest671)) => let val  result = MlyValue.BoolVarDecls (fn _
 => ([]))
 in ( LrTable.NT 7, ( result, defaultPos, defaultPos), rest671)
end
|  ( 10, ( ( _, ( MlyValue.ProcDecls ProcDecls1, _, ProcDecls1right))
 :: _ :: ( _, ( MlyValue.ProcDefs ProcDefs1, ProcDefs1left, _)) :: 
rest671)) => let val  result = MlyValue.ProcDecls (fn _ => let val  (
ProcDefs as ProcDefs1) = ProcDefs1 ()
 val  (ProcDecls as ProcDecls1) = ProcDecls1 ()
 in ((ProcDefs::ProcDecls))
end)
 in ( LrTable.NT 4, ( result, ProcDefs1left, ProcDecls1right), rest671
)
end
|  ( 11, ( rest671)) => let val  result = MlyValue.ProcDecls (fn _ =>
 (([])))
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 12, ( ( _, ( MlyValue.Block Block1, _, Block1right)) :: ( _, ( 
MlyValue.Variable Variable1, _, _)) :: ( _, ( _, PROCESS1left, _)) :: 
rest671)) => let val  result = MlyValue.ProcDefs (fn _ => let val  (
Variable as Variable1) = Variable1 ()
 val  (Block as Block1) = Block1 ()
 in (AST.Procdeff(Variable, Block))
end)
 in ( LrTable.NT 8, ( result, PROCESS1left, Block1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.VariableList VariableList1, _, 
VariableList1right)) :: _ :: ( _, ( MlyValue.Variable Variable1, 
Variable1left, _)) :: rest671)) => let val  result = 
MlyValue.VariableList (fn _ => let val  (Variable as Variable1) = 
Variable1 ()
 val  (VariableList as VariableList1) = VariableList1 ()
 in ((Variable::VariableList))
end)
 in ( LrTable.NT 10, ( result, Variable1left, VariableList1right), 
rest671)
end
|  ( 14, ( ( _, ( MlyValue.Variable Variable1, Variable1left, 
Variable1right)) :: rest671)) => let val  result = 
MlyValue.VariableList (fn _ => let val  (Variable as Variable1) = 
Variable1 ()
 in (([Variable]))
end)
 in ( LrTable.NT 10, ( result, Variable1left, Variable1right), rest671
)
end
|  ( 15, ( ( _, ( _, _, RCURLY1right)) :: ( _, ( MlyValue.Commands 
Commands1, _, _)) :: ( _, ( _, LCURLY1left, _)) :: rest671)) => let
 val  result = MlyValue.CommandSeq (fn _ => let val  (Commands as 
Commands1) = Commands1 ()
 in ((Commands))
end)
 in ( LrTable.NT 9, ( result, LCURLY1left, RCURLY1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.Commands Commands1, _, Commands1right)) ::
 _ :: ( _, ( MlyValue.Command Command1, Command1left, _)) :: rest671))
 => let val  result = MlyValue.Commands (fn _ => let val  (Command as 
Command1) = Command1 ()
 val  (Commands as Commands1) = Commands1 ()
 in ((Command::Commands))
end)
 in ( LrTable.NT 12, ( result, Command1left, Commands1right), rest671)

end
|  ( 17, ( rest671)) => let val  result = MlyValue.Commands (fn _ => (
([])))
 in ( LrTable.NT 12, ( result, defaultPos, defaultPos), rest671)
end
|  ( 18, ( ( _, ( MlyValue.RatExpression RatExpression1, _, 
RatExpression1right)) :: _ :: ( _, ( MlyValue.Variable Variable1, 
Variable1left, _)) :: rest671)) => let val  result = MlyValue.Command
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 val  (RatExpression as RatExpression1) = RatExpression1 ()
 in ((AST.AssignRat(Variable, RatExpression)))
end)
 in ( LrTable.NT 13, ( result, Variable1left, RatExpression1right), 
rest671)
end
|  ( 19, ( ( _, ( MlyValue.BoolExpression BoolExpression1, _, 
BoolExpression1right)) :: _ :: ( _, ( MlyValue.Variable Variable1, 
Variable1left, _)) :: rest671)) => let val  result = MlyValue.Command
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 val  (BoolExpression as BoolExpression1) = BoolExpression1 ()
 in ((AST.AssignBool(Variable, BoolExpression)))
end)
 in ( LrTable.NT 13, ( result, Variable1left, BoolExpression1right), 
rest671)
end
|  ( 20, ( ( _, ( MlyValue.IntExpression IntExpression1, _, 
IntExpression1right)) :: _ :: ( _, ( MlyValue.Variable Variable1, 
Variable1left, _)) :: rest671)) => let val  result = MlyValue.Command
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 val  (IntExpression as IntExpression1) = IntExpression1 ()
 in ((AST.AssignInt(Variable, IntExpression)))
end)
 in ( LrTable.NT 13, ( result, Variable1left, IntExpression1right), 
rest671)
end
|  ( 21, ( ( _, ( MlyValue.Variable Variable1, _, Variable1right)) :: 
( _, ( _, CALL1left, _)) :: rest671)) => let val  result = 
MlyValue.Command (fn _ => let val  (Variable as Variable1) = Variable1
 ()
 in ((AST.Call(Variable)))
end)
 in ( LrTable.NT 13, ( result, CALL1left, Variable1right), rest671)

end
|  ( 22, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.Variable 
Variable1, _, _)) :: _ :: ( _, ( _, CALL1left, _)) :: rest671)) => let
 val  result = MlyValue.Command (fn _ => let val  (Variable as 
Variable1) = Variable1 ()
 in ((AST.Call(Variable)))
end)
 in ( LrTable.NT 13, ( result, CALL1left, RPAREN1right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.Variable Variable1, _, Variable1right)) :: 
( _, ( _, READ1left, _)) :: rest671)) => let val  result = 
MlyValue.Command (fn _ => let val  (Variable as Variable1) = Variable1
 ()
 in ((AST.Read(Variable)))
end)
 in ( LrTable.NT 13, ( result, READ1left, Variable1right), rest671)

end
|  ( 24, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.Variable 
Variable1, _, _)) :: _ :: ( _, ( _, READ1left, _)) :: rest671)) => let
 val  result = MlyValue.Command (fn _ => let val  (Variable as 
Variable1) = Variable1 ()
 in ((AST.Read(Variable)))
end)
 in ( LrTable.NT 13, ( result, READ1left, RPAREN1right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.IntExpression IntExpression1, _, 
IntExpression1right)) :: ( _, ( _, WRITE1left, _)) :: rest671)) => let
 val  result = MlyValue.Command (fn _ => let val  (IntExpression as 
IntExpression1) = IntExpression1 ()
 in ((AST.Write(IntExpression)))
end)
 in ( LrTable.NT 13, ( result, WRITE1left, IntExpression1right), 
rest671)
end
|  ( 26, ( ( _, ( MlyValue.RatExpression RatExpression1, _, 
RatExpression1right)) :: ( _, ( _, WRITE1left, _)) :: rest671)) => let
 val  result = MlyValue.Command (fn _ => let val  (RatExpression as 
RatExpression1) = RatExpression1 ()
 in ((AST.Write(RatExpression)))
end)
 in ( LrTable.NT 13, ( result, WRITE1left, RatExpression1right), 
rest671)
end
|  ( 27, ( ( _, ( _, _, FI1right)) :: ( _, ( MlyValue.CommandSeq 
CommandSeq2, _, _)) :: _ :: ( _, ( MlyValue.CommandSeq CommandSeq1, _,
 _)) :: _ :: ( _, ( MlyValue.BoolExpression BoolExpression1, _, _)) ::
 ( _, ( _, IF1left, _)) :: rest671)) => let val  result = 
MlyValue.Command (fn _ => let val  (BoolExpression as BoolExpression1)
 = BoolExpression1 ()
 val  CommandSeq1 = CommandSeq1 ()
 val  CommandSeq2 = CommandSeq2 ()
 in ((AST.IfThenElse(BoolExpression, CommandSeq1, CommandSeq2)))
end)
 in ( LrTable.NT 13, ( result, IF1left, FI1right), rest671)
end
|  ( 28, ( ( _, ( _, _, OD1right)) :: ( _, ( MlyValue.CommandSeq 
CommandSeq1, _, _)) :: _ :: ( _, ( MlyValue.BoolExpression 
BoolExpression1, _, _)) :: ( _, ( _, WHILE1left, _)) :: rest671)) =>
 let val  result = MlyValue.Command (fn _ => let val  (BoolExpression
 as BoolExpression1) = BoolExpression1 ()
 val  (CommandSeq as CommandSeq1) = CommandSeq1 ()
 in ((AST.WhileDo(BoolExpression, CommandSeq)))
end)
 in ( LrTable.NT 13, ( result, WHILE1left, OD1right), rest671)
end
|  ( 29, ( ( _, ( MlyValue.RatTerm RatTerm1, _, RatTerm1right)) :: _
 :: ( _, ( MlyValue.RatExpression RatExpression1, RatExpression1left,
 _)) :: rest671)) => let val  result = MlyValue.RatExpression (fn _ =>
 let val  (RatExpression as RatExpression1) = RatExpression1 ()
 val  (RatTerm as RatTerm1) = RatTerm1 ()
 in ((AST.RatAdd(RatExpression, RatTerm)))
end)
 in ( LrTable.NT 15, ( result, RatExpression1left, RatTerm1right), 
rest671)
end
|  ( 30, ( ( _, ( MlyValue.RatTerm RatTerm1, _, RatTerm1right)) :: _
 :: ( _, ( MlyValue.RatExpression RatExpression1, RatExpression1left,
 _)) :: rest671)) => let val  result = MlyValue.RatExpression (fn _ =>
 let val  (RatExpression as RatExpression1) = RatExpression1 ()
 val  (RatTerm as RatTerm1) = RatTerm1 ()
 in ((AST.RatSub(RatExpression, RatTerm)))
end)
 in ( LrTable.NT 15, ( result, RatExpression1left, RatTerm1right), 
rest671)
end
|  ( 31, ( ( _, ( MlyValue.RatTerm RatTerm1, RatTerm1left, 
RatTerm1right)) :: rest671)) => let val  result = 
MlyValue.RatExpression (fn _ => let val  (RatTerm as RatTerm1) = 
RatTerm1 ()
 in ((RatTerm))
end)
 in ( LrTable.NT 15, ( result, RatTerm1left, RatTerm1right), rest671)

end
|  ( 32, ( ( _, ( MlyValue.IntTerm IntTerm1, _, IntTerm1right)) :: _
 :: ( _, ( MlyValue.IntExpression IntExpression1, IntExpression1left,
 _)) :: rest671)) => let val  result = MlyValue.IntExpression (fn _ =>
 let val  (IntExpression as IntExpression1) = IntExpression1 ()
 val  (IntTerm as IntTerm1) = IntTerm1 ()
 in ((AST.Add(IntExpression, IntTerm)))
end)
 in ( LrTable.NT 14, ( result, IntExpression1left, IntTerm1right), 
rest671)
end
|  ( 33, ( ( _, ( MlyValue.IntTerm IntTerm1, _, IntTerm1right)) :: _
 :: ( _, ( MlyValue.IntExpression IntExpression1, IntExpression1left,
 _)) :: rest671)) => let val  result = MlyValue.IntExpression (fn _ =>
 let val  (IntExpression as IntExpression1) = IntExpression1 ()
 val  (IntTerm as IntTerm1) = IntTerm1 ()
 in ((AST.Sub(IntExpression, IntTerm)))
end)
 in ( LrTable.NT 14, ( result, IntExpression1left, IntTerm1right), 
rest671)
end
|  ( 34, ( ( _, ( MlyValue.IntTerm IntTerm1, IntTerm1left, 
IntTerm1right)) :: rest671)) => let val  result = 
MlyValue.IntExpression (fn _ => let val  (IntTerm as IntTerm1) = 
IntTerm1 ()
 in ((IntTerm))
end)
 in ( LrTable.NT 14, ( result, IntTerm1left, IntTerm1right), rest671)

end
|  ( 35, ( ( _, ( MlyValue.RatFactor RatFactor1, _, RatFactor1right))
 :: _ :: ( _, ( MlyValue.RatTerm RatTerm1, RatTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.RatTerm (fn _ => let val  (
RatTerm as RatTerm1) = RatTerm1 ()
 val  (RatFactor as RatFactor1) = RatFactor1 ()
 in ((AST.RatMul(RatTerm, RatFactor)))
end)
 in ( LrTable.NT 18, ( result, RatTerm1left, RatFactor1right), rest671
)
end
|  ( 36, ( ( _, ( MlyValue.RatFactor RatFactor1, _, RatFactor1right))
 :: _ :: ( _, ( MlyValue.RatTerm RatTerm1, RatTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.RatTerm (fn _ => let val  (
RatTerm as RatTerm1) = RatTerm1 ()
 val  (RatFactor as RatFactor1) = RatFactor1 ()
 in ((AST.RatDiv(RatTerm, RatFactor)))
end)
 in ( LrTable.NT 18, ( result, RatTerm1left, RatFactor1right), rest671
)
end
|  ( 37, ( ( _, ( MlyValue.RatFactor RatFactor1, RatFactor1left, 
RatFactor1right)) :: rest671)) => let val  result = MlyValue.RatTerm
 (fn _ => let val  (RatFactor as RatFactor1) = RatFactor1 ()
 in ((RatFactor))
end)
 in ( LrTable.NT 18, ( result, RatFactor1left, RatFactor1right), 
rest671)
end
|  ( 38, ( ( _, ( MlyValue.IntFactor IntFactor1, _, IntFactor1right))
 :: _ :: ( _, ( MlyValue.IntTerm IntTerm1, IntTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.IntTerm (fn _ => let val  (
IntTerm as IntTerm1) = IntTerm1 ()
 val  (IntFactor as IntFactor1) = IntFactor1 ()
 in ((AST.Multiply(IntTerm, IntFactor)))
end)
 in ( LrTable.NT 17, ( result, IntTerm1left, IntFactor1right), rest671
)
end
|  ( 39, ( ( _, ( MlyValue.IntFactor IntFactor1, _, IntFactor1right))
 :: _ :: ( _, ( MlyValue.IntTerm IntTerm1, IntTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.IntTerm (fn _ => let val  (
IntTerm as IntTerm1) = IntTerm1 ()
 val  (IntFactor as IntFactor1) = IntFactor1 ()
 in ((AST.Divide(IntTerm, IntFactor)))
end)
 in ( LrTable.NT 17, ( result, IntTerm1left, IntFactor1right), rest671
)
end
|  ( 40, ( ( _, ( MlyValue.IntFactor IntFactor1, _, IntFactor1right))
 :: _ :: ( _, ( MlyValue.IntTerm IntTerm1, IntTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.IntTerm (fn _ => let val  (
IntTerm as IntTerm1) = IntTerm1 ()
 val  (IntFactor as IntFactor1) = IntFactor1 ()
 in ((AST.Modulo(IntTerm, IntFactor)))
end)
 in ( LrTable.NT 17, ( result, IntTerm1left, IntFactor1right), rest671
)
end
|  ( 41, ( ( _, ( MlyValue.IntFactor IntFactor1, IntFactor1left, 
IntFactor1right)) :: rest671)) => let val  result = MlyValue.IntTerm
 (fn _ => let val  (IntFactor as IntFactor1) = IntFactor1 ()
 in ((IntFactor))
end)
 in ( LrTable.NT 17, ( result, IntFactor1left, IntFactor1right), 
rest671)
end
|  ( 42, ( ( _, ( MlyValue.NUMERAL NUMERAL1, NUMERAL1left, 
NUMERAL1right)) :: rest671)) => let val  result = MlyValue.IntFactor
 (fn _ => let val  (NUMERAL as NUMERAL1) = NUMERAL1 ()
 in ((AST.Num(NUMERAL)))
end)
 in ( LrTable.NT 19, ( result, NUMERAL1left, NUMERAL1right), rest671)

end
|  ( 43, ( ( _, ( MlyValue.Variable Variable1, Variable1left, 
Variable1right)) :: rest671)) => let val  result = MlyValue.IntFactor
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 in ((Variable))
end)
 in ( LrTable.NT 19, ( result, Variable1left, Variable1right), rest671
)
end
|  ( 44, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.IntExpression IntExpression1, _, _)) :: ( _, ( _, LPAREN1left
, _)) :: rest671)) => let val  result = MlyValue.IntFactor (fn _ =>
 let val  (IntExpression as IntExpression1) = IntExpression1 ()
 in ((IntExpression))
end)
 in ( LrTable.NT 19, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 45, ( ( _, ( MlyValue.IntFactor IntFactor1, _, IntFactor1right))
 :: ( _, ( _, NEG1left, _)) :: rest671)) => let val  result = 
MlyValue.IntFactor (fn _ => let val  (IntFactor as IntFactor1) = 
IntFactor1 ()
 in ((AST.Neg(IntFactor)))
end)
 in ( LrTable.NT 19, ( result, NEG1left, IntFactor1right), rest671)

end
|  ( 46, ( ( _, ( MlyValue.IntFactor IntFactor1, _, IntFactor1right))
 :: ( _, ( _, PLUS1left, _)) :: rest671)) => let val  result = 
MlyValue.IntFactor (fn _ => let val  (IntFactor as IntFactor1) = 
IntFactor1 ()
 in ((IntFactor))
end)
 in ( LrTable.NT 19, ( result, PLUS1left, IntFactor1right), rest671)

end
|  ( 47, ( ( _, ( MlyValue.RATVAL RATVAL1, RATVAL1left, RATVAL1right))
 :: rest671)) => let val  result = MlyValue.RatFactor (fn _ => let
 val  (RATVAL as RATVAL1) = RATVAL1 ()
 in ((AST.Rat(RATVAL)))
end)
 in ( LrTable.NT 20, ( result, RATVAL1left, RATVAL1right), rest671)

end
|  ( 48, ( ( _, ( MlyValue.Variable Variable1, Variable1left, 
Variable1right)) :: rest671)) => let val  result = MlyValue.RatFactor
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 in ((Variable))
end)
 in ( LrTable.NT 20, ( result, Variable1left, Variable1right), rest671
)
end
|  ( 49, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.RatExpression RatExpression1, _, _)) :: ( _, ( _, LPAREN1left
, _)) :: rest671)) => let val  result = MlyValue.RatFactor (fn _ =>
 let val  (RatExpression as RatExpression1) = RatExpression1 ()
 in ((RatExpression))
end)
 in ( LrTable.NT 20, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 50, ( ( _, ( MlyValue.RatFactor RatFactor1, _, RatFactor1right))
 :: ( _, ( _, NEG1left, _)) :: rest671)) => let val  result = 
MlyValue.RatFactor (fn _ => let val  (RatFactor as RatFactor1) = 
RatFactor1 ()
 in ((AST.Neg(RatFactor)))
end)
 in ( LrTable.NT 20, ( result, NEG1left, RatFactor1right), rest671)

end
|  ( 51, ( ( _, ( MlyValue.RatFactor RatFactor1, _, RatFactor1right))
 :: ( _, ( _, PLUS1left, _)) :: rest671)) => let val  result = 
MlyValue.RatFactor (fn _ => let val  (RatFactor as RatFactor1) = 
RatFactor1 ()
 in ((RatFactor))
end)
 in ( LrTable.NT 20, ( result, PLUS1left, RatFactor1right), rest671)

end
|  ( 52, ( ( _, ( MlyValue.DecimalForm DecimalForm1, _, 
DecimalForm1right)) :: ( _, ( _, FROMDEC1left, _)) :: rest671)) => let
 val  result = MlyValue.RatFactor (fn _ => let val  (DecimalForm as 
DecimalForm1) = DecimalForm1 ()
 in ((DecimalForm))
end)
 in ( LrTable.NT 20, ( result, FROMDEC1left, DecimalForm1right), 
rest671)
end
|  ( 53, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.DecimalForm 
DecimalForm1, _, _)) :: _ :: ( _, ( _, FROMDEC1left, _)) :: rest671))
 => let val  result = MlyValue.RatFactor (fn _ => let val  (
DecimalForm as DecimalForm1) = DecimalForm1 ()
 in ((DecimalForm))
end)
 in ( LrTable.NT 20, ( result, FROMDEC1left, RPAREN1right), rest671)

end
|  ( 54, ( ( _, ( MlyValue.RationalForm RationalForm1, _, 
RationalForm1right)) :: ( _, ( _, MKRAT1left, _)) :: rest671)) => let
 val  result = MlyValue.RatFactor (fn _ => let val  (RationalForm as 
RationalForm1) = RationalForm1 ()
 in ((RationalForm))
end)
 in ( LrTable.NT 20, ( result, MKRAT1left, RationalForm1right), 
rest671)
end
|  ( 55, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.RationalForm
 RationalForm1, _, _)) :: _ :: ( _, ( _, MKRAT1left, _)) :: rest671))
 => let val  result = MlyValue.RatFactor (fn _ => let val  (
RationalForm as RationalForm1) = RationalForm1 ()
 in ((RationalForm))
end)
 in ( LrTable.NT 20, ( result, MKRAT1left, RPAREN1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.BoolTerm BoolTerm1, _, BoolTerm1right)) ::
 _ :: ( _, ( MlyValue.BoolExpression BoolExpression1, 
BoolExpression1left, _)) :: rest671)) => let val  result = 
MlyValue.BoolExpression (fn _ => let val  (BoolExpression as 
BoolExpression1) = BoolExpression1 ()
 val  (BoolTerm as BoolTerm1) = BoolTerm1 ()
 in ((AST.Or(BoolExpression, BoolTerm)))
end)
 in ( LrTable.NT 16, ( result, BoolExpression1left, BoolTerm1right), 
rest671)
end
|  ( 57, ( ( _, ( MlyValue.BoolTerm BoolTerm1, BoolTerm1left, 
BoolTerm1right)) :: rest671)) => let val  result = 
MlyValue.BoolExpression (fn _ => let val  (BoolTerm as BoolTerm1) = 
BoolTerm1 ()
 in ((BoolTerm))
end)
 in ( LrTable.NT 16, ( result, BoolTerm1left, BoolTerm1right), rest671
)
end
|  ( 58, ( ( _, ( MlyValue.BoolFactor BoolFactor1, _, BoolFactor1right
)) :: _ :: ( _, ( MlyValue.BoolTerm BoolTerm1, BoolTerm1left, _)) :: 
rest671)) => let val  result = MlyValue.BoolTerm (fn _ => let val  (
BoolTerm as BoolTerm1) = BoolTerm1 ()
 val  (BoolFactor as BoolFactor1) = BoolFactor1 ()
 in ((AST.And(BoolTerm, BoolFactor)))
end)
 in ( LrTable.NT 21, ( result, BoolTerm1left, BoolFactor1right), 
rest671)
end
|  ( 59, ( ( _, ( MlyValue.BoolFactor BoolFactor1, BoolFactor1left, 
BoolFactor1right)) :: rest671)) => let val  result = MlyValue.BoolTerm
 (fn _ => let val  (BoolFactor as BoolFactor1) = BoolFactor1 ()
 in ((BoolFactor))
end)
 in ( LrTable.NT 21, ( result, BoolFactor1left, BoolFactor1right), 
rest671)
end
|  ( 60, ( ( _, ( _, TT1left, TT1right)) :: rest671)) => let val  
result = MlyValue.BoolFactor (fn _ => ((AST.Bool(true))))
 in ( LrTable.NT 22, ( result, TT1left, TT1right), rest671)
end
|  ( 61, ( ( _, ( _, FF1left, FF1right)) :: rest671)) => let val  
result = MlyValue.BoolFactor (fn _ => ((AST.Bool(false))))
 in ( LrTable.NT 22, ( result, FF1left, FF1right), rest671)
end
|  ( 62, ( ( _, ( MlyValue.Variable Variable1, Variable1left, 
Variable1right)) :: rest671)) => let val  result = MlyValue.BoolFactor
 (fn _ => let val  (Variable as Variable1) = Variable1 ()
 in ((Variable))
end)
 in ( LrTable.NT 22, ( result, Variable1left, Variable1right), rest671
)
end
|  ( 63, ( ( _, ( MlyValue.Comparison Comparison1, Comparison1left, 
Comparison1right)) :: rest671)) => let val  result = 
MlyValue.BoolFactor (fn _ => let val  (Comparison as Comparison1) = 
Comparison1 ()
 in ((Comparison))
end)
 in ( LrTable.NT 22, ( result, Comparison1left, Comparison1right), 
rest671)
end
|  ( 64, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.BoolExpression BoolExpression1, _, _)) :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.BoolFactor
 (fn _ => let val  (BoolExpression as BoolExpression1) = 
BoolExpression1 ()
 in ((BoolExpression))
end)
 in ( LrTable.NT 22, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 65, ( ( _, ( MlyValue.BoolFactor BoolFactor1, _, BoolFactor1right
)) :: ( _, ( _, NOT1left, _)) :: rest671)) => let val  result = 
MlyValue.BoolFactor (fn _ => let val  (BoolFactor as BoolFactor1) = 
BoolFactor1 ()
 in ((AST.Not(BoolFactor)))
end)
 in ( LrTable.NT 22, ( result, NOT1left, BoolFactor1right), rest671)

end
|  ( 66, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.LessThan(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 67, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.LessThanEq(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 68, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.Equals(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 69, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.NotEqual(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 70, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.GreaterThan(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 71, ( ( _, ( MlyValue.IntExpression IntExpression2, _, 
IntExpression2right)) :: _ :: ( _, ( MlyValue.IntExpression 
IntExpression1, IntExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  IntExpression1 = 
IntExpression1 ()
 val  IntExpression2 = IntExpression2 ()
 in ((AST.GreaterThanEq(IntExpression1, IntExpression2)))
end)
 in ( LrTable.NT 23, ( result, IntExpression1left, IntExpression2right
), rest671)
end
|  ( 72, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.LessThan(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 73, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.LessThanEq(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 74, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.Equals(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 75, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.NotEqual(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 76, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.GreaterThan(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 77, ( ( _, ( MlyValue.RatExpression RatExpression2, _, 
RatExpression2right)) :: _ :: ( _, ( MlyValue.RatExpression 
RatExpression1, RatExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  RatExpression1 = 
RatExpression1 ()
 val  RatExpression2 = RatExpression2 ()
 in ((AST.GreaterThanEq(RatExpression1, RatExpression2)))
end)
 in ( LrTable.NT 23, ( result, RatExpression1left, RatExpression2right
), rest671)
end
|  ( 78, ( ( _, ( MlyValue.BoolExpression BoolExpression2, _, 
BoolExpression2right)) :: _ :: ( _, ( MlyValue.BoolExpression 
BoolExpression1, BoolExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  BoolExpression1 = 
BoolExpression1 ()
 val  BoolExpression2 = BoolExpression2 ()
 in ((AST.Equals(BoolExpression1, BoolExpression2)))
end)
 in ( LrTable.NT 23, ( result, BoolExpression1left, 
BoolExpression2right), rest671)
end
|  ( 79, ( ( _, ( MlyValue.BoolExpression BoolExpression2, _, 
BoolExpression2right)) :: _ :: ( _, ( MlyValue.BoolExpression 
BoolExpression1, BoolExpression1left, _)) :: rest671)) => let val  
result = MlyValue.Comparison (fn _ => let val  BoolExpression1 = 
BoolExpression1 ()
 val  BoolExpression2 = BoolExpression2 ()
 in ((AST.NotEqual(BoolExpression1, BoolExpression2)))
end)
 in ( LrTable.NT 23, ( result, BoolExpression1left, 
BoolExpression2right), rest671)
end
|  ( 80, ( ( _, ( MlyValue.IDENTIFIER IDENTIFIER1, IDENTIFIER1left, 
IDENTIFIER1right)) :: rest671)) => let val  result = MlyValue.Variable
 (fn _ => let val  (IDENTIFIER as IDENTIFIER1) = IDENTIFIER1 ()
 in ((AST.Variable(IDENTIFIER)))
end)
 in ( LrTable.NT 11, ( result, IDENTIFIER1left, IDENTIFIER1right), 
rest671)
end
|  ( 81, ( ( _, ( MlyValue.RATDECFORM RATDECFORM1, RATDECFORM1left, 
RATDECFORM1right)) :: rest671)) => let val  result = 
MlyValue.DecimalForm (fn _ => let val  (RATDECFORM as RATDECFORM1) = 
RATDECFORM1 ()
 in ((AST.DecimalForm(RATDECFORM)))
end)
 in ( LrTable.NT 24, ( result, RATDECFORM1left, RATDECFORM1right), 
rest671)
end
|  ( 82, ( ( _, ( MlyValue.RATVAL RATVAL1, RATVAL1left, RATVAL1right))
 :: rest671)) => let val  result = MlyValue.RationalForm (fn _ => let
 val  (RATVAL as RATVAL1) = RATVAL1 ()
 in ((AST.RationalForm(RATVAL)))
end)
 in ( LrTable.NT 25, ( result, RATVAL1left, RATVAL1right), rest671)

end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.Program x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : While_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun LCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun RCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun ASSIGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun MUL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun RATMUL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun DIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun RATDIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun MOD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun RATPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun RATMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun GT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun LE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun GE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun NE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun NEG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun INV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun PROCESS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun VAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun RATIONAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun BOOL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun MKRAT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun RAT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun SHOWDEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun FROMDEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun TODEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun SHOWRAT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID,p1,p2))
fun READ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID,p1,p2))
fun WRITE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID,p1,p2))
fun CALL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID,p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID,p1,p2))
fun FI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID,p1,p2))
fun WHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID,p1,p2))
fun DO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID,p1,p2))
fun OD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(
ParserData.MlyValue.VOID,p1,p2))
fun TT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(
ParserData.MlyValue.VOID,p1,p2))
fun FF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(
ParserData.MlyValue.VOID,p1,p2))
fun RATVAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(
ParserData.MlyValue.RATVAL (fn () => i),p1,p2))
fun RATDECFORM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 51,(
ParserData.MlyValue.RATDECFORM (fn () => i),p1,p2))
fun IDENTIFIER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 52,(
ParserData.MlyValue.IDENTIFIER (fn () => i),p1,p2))
fun NUMERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 53,(
ParserData.MlyValue.NUMERAL (fn () => i),p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 54,(
ParserData.MlyValue.VOID,p1,p2))
fun BADCH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 55,(
ParserData.MlyValue.VOID,p1,p2))
end
end
