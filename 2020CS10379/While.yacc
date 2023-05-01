%%
%name While
%term SEMICOLON
      | COMMA
      | LCURLY
      | RCURLY
      | ASSIGN
      | LPAREN
      | RPAREN
      | OR
      | AND
      | NOT
      | MUL
      | RATMUL
      | DIV
      | RATDIV
      | MOD
      | PLUS
      | RATPLUS
      | MINUS
      | RATMINUS
      | LT
      | GT
      | LE
      | GE
      | EQ
      | NE
      | NEG
      | INV
      | PROCESS
      | VAR
      | RATIONAL
      | INT
      | BOOL
      | MKRAT
      | RAT
      | SHOWDEC
      | FROMDEC
      | TODEC
      | SHOWRAT
      | READ
      | WRITE
      | CALL
      | IF
      | THEN
      | ELSE
      | FI
      | WHILE
      | DO
      | OD
      | TT
      | FF
      | RATVAL of string
      | RATDECFORM of string
      | IDENTIFIER of string
      | NUMERAL of BigInt.bigint
      | EOF
      | BADCH
    
%nonterm Program of AST.AST
       | Block of ((AST.AST list *  AST.AST list * AST.AST list) * AST.AST list) * AST.AST list
       | DeclarationSeq of (AST.AST list *  AST.AST list * AST.AST list) * AST.AST list
       | VarDecls of AST.AST list *  AST.AST list * AST.AST list
       | ProcDecls of AST.AST list
       | RatVarDecls of AST.AST list
       | IntVarDecls of AST.AST list
       | BoolVarDecls of AST.AST list
       | ProcDefs of AST.AST
       | CommandSeq of AST.AST list
       | VariableList of AST.AST list
       | Variable of AST.AST
       | Commands of AST.AST list
       | Command of AST.AST
       | IntExpression of AST.AST
       | RatExpression of AST.AST
       | BoolExpression of AST.AST
       | IntTerm of AST.AST
       | RatTerm of AST.AST
       | IntFactor of AST.AST
       | RatFactor of AST.AST
       | BoolTerm of AST.AST
       | BoolFactor of AST.AST
       | Comparison of AST.AST
       | DecimalForm of AST.AST
       | RationalForm of AST.AST

%start Program
%pos int
%eop EOF
%noshift EOF
%verbose
(* %keyword PROCESS VAR RATIONAL RAT INT BOOL READ WRITE CALL IF THEN ELSE FI WHILE DO OD TT FF RAT *)
%arg (fileName) : string

%%
Program: Block ((AST.Procdeff(AST.Variable("_main"),Block)))
Block: DeclarationSeq CommandSeq ((DeclarationSeq, CommandSeq))
DeclarationSeq: VarDecls ProcDecls ((VarDecls, ProcDecls))
VarDecls: RatVarDecls IntVarDecls BoolVarDecls ((RatVarDecls, IntVarDecls, BoolVarDecls))
RatVarDecls: RATIONAL VariableList SEMICOLON ((VariableList)) 
      | ([])
IntVarDecls: INT VariableList SEMICOLON ((VariableList)) 
      | ([])
BoolVarDecls: BOOL VariableList SEMICOLON ((VariableList)) 
      | ([])
ProcDecls: ProcDefs SEMICOLON ProcDecls ((ProcDefs::ProcDecls)) | (([]))
ProcDefs: PROCESS Variable Block (AST.Procdeff(Variable, Block))
VariableList: Variable COMMA VariableList ((Variable::VariableList))
            | Variable (([Variable]))
CommandSeq: LCURLY Commands RCURLY ((Commands))
Commands: Command SEMICOLON Commands ((Command::Commands))
      | (([]))
Command: Variable ASSIGN RatExpression ((AST.AssignRat(Variable, RatExpression)))
      |Variable ASSIGN BoolExpression ((AST.AssignBool(Variable, BoolExpression)))
      | Variable ASSIGN IntExpression ((AST.AssignInt(Variable, IntExpression)))
      | CALL Variable ((AST.Call(Variable)))
      | CALL LPAREN Variable RPAREN ((AST.Call(Variable)))
      | READ Variable ((AST.Read(Variable)))
      | READ LPAREN Variable RPAREN ((AST.Read(Variable)))
      | WRITE IntExpression ((AST.Write(IntExpression)))
      | WRITE RatExpression ((AST.Write(RatExpression)))
      | IF BoolExpression THEN CommandSeq ELSE CommandSeq FI ((AST.IfThenElse(BoolExpression, CommandSeq1, CommandSeq2)))
      | WHILE BoolExpression DO CommandSeq OD ((AST.WhileDo(BoolExpression, CommandSeq)))
RatExpression: RatExpression RATPLUS RatTerm ((AST.RatAdd(RatExpression, RatTerm)))
            | RatExpression RATMINUS RatTerm ((AST.RatSub(RatExpression, RatTerm)))
            | RatTerm ((RatTerm))
IntExpression: IntExpression PLUS IntTerm ((AST.Add(IntExpression, IntTerm)))
            | IntExpression MINUS IntTerm ((AST.Sub(IntExpression, IntTerm)))
            | IntTerm   ((IntTerm))
RatTerm: RatTerm RATMUL RatFactor ((AST.RatMul(RatTerm, RatFactor)))
      | RatTerm RATDIV RatFactor ((AST.RatDiv(RatTerm, RatFactor)))  
      | RatFactor ((RatFactor))          
IntTerm: IntTerm MUL IntFactor ((AST.Multiply(IntTerm, IntFactor)))
      | IntTerm DIV IntFactor ((AST.Divide(IntTerm, IntFactor)))
      | IntTerm MOD IntFactor ((AST.Modulo(IntTerm, IntFactor)))
      | IntFactor ((IntFactor))
IntFactor: NUMERAL ((AST.Num(NUMERAL)))
      | Variable ((Variable))
      | LPAREN IntExpression RPAREN ((IntExpression))
      | NEG IntFactor ((AST.Neg(IntFactor)))
      | PLUS IntFactor ((IntFactor))
RatFactor: RATVAL ((AST.Rat(RATVAL)))
      | Variable ((Variable))
      | LPAREN RatExpression RPAREN ((RatExpression))
      | NEG RatFactor ((AST.Neg(RatFactor)))
      | PLUS RatFactor ((RatFactor))
      | FROMDEC DecimalForm ((DecimalForm))
      | FROMDEC LPAREN DecimalForm RPAREN ((DecimalForm))
      | MKRAT RationalForm ((RationalForm))
      | MKRAT LPAREN RationalForm RPAREN ((RationalForm))
BoolExpression: BoolExpression OR BoolTerm ((AST.Or(BoolExpression, BoolTerm)))
            | BoolTerm ((BoolTerm))
BoolTerm: BoolTerm AND BoolFactor ((AST.And(BoolTerm, BoolFactor)))
      | BoolFactor ((BoolFactor))    
BoolFactor: TT ((AST.Bool(true)))
      | FF ((AST.Bool(false)))
      | Variable ((Variable))
      | Comparison ((Comparison))
      | LPAREN BoolExpression RPAREN ((BoolExpression))
      | NOT BoolFactor ((AST.Not(BoolFactor)))
Comparison: IntExpression LT IntExpression ((AST.LessThan(IntExpression1, IntExpression2)))
      | IntExpression LE IntExpression ((AST.LessThanEq(IntExpression1, IntExpression2)))
      | IntExpression EQ IntExpression ((AST.Equals(IntExpression1, IntExpression2)))
      | IntExpression NE IntExpression ((AST.NotEqual(IntExpression1, IntExpression2)))
      | IntExpression GT IntExpression ((AST.GreaterThan(IntExpression1, IntExpression2)))
      | IntExpression GE IntExpression ((AST.GreaterThanEq(IntExpression1, IntExpression2)))
      | RatExpression LT RatExpression ((AST.LessThan(RatExpression1, RatExpression2)))
      | RatExpression LE RatExpression ((AST.LessThanEq(RatExpression1, RatExpression2)))
      | RatExpression EQ RatExpression ((AST.Equals(RatExpression1, RatExpression2)))
      | RatExpression NE RatExpression ((AST.NotEqual(RatExpression1, RatExpression2)))
      | RatExpression GT RatExpression ((AST.GreaterThan(RatExpression1, RatExpression2)))
      | RatExpression GE RatExpression ((AST.GreaterThanEq(RatExpression1, RatExpression2)))
      | BoolExpression EQ BoolExpression ((AST.Equals(BoolExpression1, BoolExpression2)))
      | BoolExpression NE BoolExpression ((AST.NotEqual(BoolExpression1, BoolExpression2)))
Variable: IDENTIFIER ((AST.Variable(IDENTIFIER)))
DecimalForm: RATDECFORM ((AST.DecimalForm(RATDECFORM)))
RationalForm: RATVAL ((AST.RationalForm(RATVAL)))