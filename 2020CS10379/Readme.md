
## Important files:
 `While.lex` : It contains definitions, declarations and rules for creating lexer for while language
 `While.yacc`: It contains definitions, declarations and rules for creating parser for while language
 `compiler.sml`: It contains structure to compile While programs
 `glue.sml`: It combines `While.lex` and `While.yacc`
 `datatypes.sml`: It defines Abstract Syntax Tree Data Structure
 `MakeFile`: It runs lexer and parser and creates compiler which outputs Abstract Syntax Tree
 `While.cm`: It create a structure for While language and provides basis library, ml-lex and ml-yacc library
 `while_ast.sml`: It contains functions to convert AST into postfix and insert in control stack and function to execute it;
 `memory.sml`: It defines memory ast list of (AST.AST * int)
 `stack.sml`: It defines signature and structure of stack

## How to run parser:
- type `make` in command line - terminal.
- After that copy tree from AST to while_ast.sml MyP
- run `make` again in command line -terminal.
- type execute MyP to run the program.

## CONTEXT-FREE GRAMMAR
- Terminals
```sh
    SEMICOLON
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
      | DOLLAR
      | RATVAL of string
      | IDENTIFIER of string
      | NUMERAL of BigInt
      | EOF
      | BADCH
```
- NonTerminals
```
    Program of AST.AST
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
 ```
- Start Symbol `Program`

- Production Rules:
```
Program         ::= Block '.' 

Block           ::= DeclarationSeq CommandSeq 

DeclarationSeq  ::= VarDecls ProcDecls | ProcDecls VarDecls | VarDecls | ε

VarDecls        ::= RatVarDecls IntVarDecls BoolVarDecls

RatVarDecls     ::= 'rational' IdentList ';'

IntVarDecls     ::= 'integer' IdentList ';'

BoolVarDecls    ::= 'boolean' IdentList ';'

IdentList       ::= Ident { ',' Ident }

ProcDecls       ::= ProcDef ';' ProcDecls | ProcDef 

ProcDef         ::= 'procedure' Ident Block 

CommandSeq      ::= Command ';' CommandSeq | Command 

Command         ::= AssignmentCmd | CallCmd | ReadCmd | PrintCmd | ConditionalCmd | WhileCmd 

AssignmentCmd   ::= Ident ':=' Expression 

CallCmd         ::= 'call' Ident 

ReadCmd         ::= 'read' '(' Ident ')' 

PrintCmd        ::= 'print' '(' Expression ')' 

Expression      ::= RatExpression | IntExpression | BoolExpression 

RatExpression   ::= IntExpression | IntExpression RatBinOp RatTerm | RatUnOp RatTerm

IntExpression   ::= BoolExpression | BoolExpression IntBinOp IntTerm 

BoolExpression  ::= 'true' | 'false' | Relation | BoolUnOp BoolExpression | '(' BoolExpression ')'

Relation        ::= SimpleExpression RelOp SimpleExpression 

SimpleExpression::= Term | SimpleExpression AddOp Term 

Term            ::= Factor | Term MulOp Factor 

Factor          ::= Ident | Literal | '(' Expression ')' 

Ident           ::= letter { ( letter | digit | '_' ) } 

Literal         ::= integer | rational | 'tt' | 'ff'

RatBinOp        ::= '.+.' | '.-.' | '.*.' | './.' 

RatUnOp         ::= 'make rat' | 'rat' | 'showRat' | 'showDecimal' | 'fromDecimal' | 'toDecimal' | '~' | '+' | 'inverse' 

IntBinOp        ::= '+' | '-' | '*' | '/' | '%' 

BoolUnOp        ::= '!' 

AddOp           ::= '+' | '-' | 'or' 

MulOp           ::= '*' | '/' | 'and' 

RelOp           ::= '=' | '<>' | '<' | '>' | '<=' | '>=' 

letter          ::= 'a' .. 'z' | 'A' .. 'Z' 

digit           ::= '0' .. '9' 

Comment         ::= '(' ( any printable ASCII character ) '*)'
```

- Syntax-Directed Translation:
```
Program: Block ((AST.Program(Block)))
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
            |  (([]))
CommandSeq: LCURLY Commands RCURLY ((Commands))
Commands: Command SEMICOLON Commands ((Command::Commands))
      | DOLLAR (([]))
Command: Variable ASSIGN BoolExpression ((AST.AssignBool(Variable, BoolExpression)))
      | Variable ASSIGN IntExpression ((AST.AssignInt(Variable, IntExpression)))
      | Variable ASSIGN RatExpression ((AST.AssignRat(Variable, RatExpression)))
      | CALL Variable ((AST.Call(Variable)))
      | READ Variable ((AST.Read(Variable)))
      | WRITE IntExpression ((AST.Write(IntExpression)))
      | WRITE RatExpression ((AST.Write(RatExpression)))
      | IF BoolExpression THEN CommandSeq ELSE CommandSeq FI ((AST.IfThenElse(BoolExpression, CommandSeq1, CommandSeq2)))
      | WHILE BoolExpression DO CommandSeq OD ((AST.WhileDo(BoolExpression, CommandSeq)))
IntExpression: IntExpression PLUS IntTerm ((AST.Add(IntExpression, IntTerm)))
            | IntExpression MINUS IntTerm ((AST.Sub(IntExpression, IntTerm)))
            | IntTerm   ((IntTerm))
RatExpression: RatExpression RATPLUS RatTerm ((AST.RatAdd(RatExpression, RatTerm)))
            | RatExpression RATMINUS RatTerm ((AST.RatSub(RatExpression, RatTerm)))
            | RatTerm ((RatTerm))
IntTerm: IntTerm MUL IntFactor ((AST.Multiply(IntTerm, IntFactor)))
      | IntTerm DIV IntFactor ((AST.Divide(IntTerm, IntFactor)))
      | IntTerm MOD IntFactor ((AST.Modulo(IntTerm, IntFactor)))
      | IntFactor ((IntFactor))
RatTerm: RatTerm RATMUL RatFactor ((AST.RatMul(RatTerm, RatFactor)))
      | RatTerm RATDIV RatFactor ((AST.RatDiv(RatTerm, RatFactor)))
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
Variable: IDENTIFIER ((AST.Variable(IDENTIFIER)))
```
## DATATYPES
```
    type IDENTIFIER = string
    type NUMERAL = int
    datatype Program = Program of Keyword * IDENTIFIER * Symbol * Block
    and      Block = Block0 of DeclarationSeq * CommandSeq
                  | Block1 of CommandSeq
    and      DeclarationSeq = DeclarationSeq0 of Declaration
                          | DeclarationSeq1 of Declaration * DeclarationSeq
    and      Declaration = Declaration of Keyword * VariableList * Symbol * Type * Symbol
    and      Type = INT
                  | BOOL
    and      VariableList  = VariableList1 of Variable * Symbol * VariableList
                        | VariableList0 of Variable
    and      CommandSeq = CommandSeq of Symbol * Commands * Symbol
    and      Commands = Commands0 of Command
                    | Commands1 of Command * Symbol * Commands
    and      Command = Command0 of Variable * Symbol * Expression
                    | Command1 of Keyword * Variable
                    | Command2 of Keyword * IntExpression
                    | Command3 of Keyword * BoolExpression * Keyword * CommandSeq * Keyword * CommandSeq * Keyword
                    | Command4 of Keyword * BoolExpression * Keyword * CommandSeq * Keyword
    and      Expression = Expression0 of IntExpression
                      | Expression1 of BoolExpression
    and      IntExpression = IntExpression0 of IntExpression * AddOp * IntTerm
                          | IntExpression1 of IntTerm
    and      IntTerm = IntTerm0 of IntTerm * MultOp * IntFactor
                    | IntTerm1 of IntFactor
    and      IntFactor = IntFactor0 of NUMERAL
                      | IntFactor1 of Variable
                      | IntFactor2 of Symbol * IntExpression * Symbol
    and      BoolExpression = BoolExpression0 of BoolExpression * Symbol * BoolTerm
                          | BoolExpression1 of BoolTerm
    and      BoolTerm = BoolTerm0 of BoolTerm * Symbol * BoolFactor
                    | BoolTerm1 of BoolFactor
    and      BoolFactor = BoolFactor0 of Keyword
                      | BoolFactor1 of Variable
                      | BoolFactor2 of Comparison
                      | BoolFactor3 of Symbol * BoolExpression * Symbol
                      | BoolFactor4 of Symbol * BoolFactor
    and Comparison = Comparison of IntExpression * RelOp * IntExpression
    and Variable = Variable of IDENTIFIER
    and RelOp = LT
              | LE
              | GT
              | GE
              | EQ
              | NE
    and AddOp = PLUS
              | MINUS
    and MultOp = MUL
              | DIV
              | MOD
    and Symbol = DCOLON 
              | COMMA 
              | LCURLY 
              | RCURLY 
              | COLON
              | SEMICOLON 
              | ASSIGN 
              | LPAREN 
              | RPAREN 
              | OR
              | AND
              | NOT
              | NEG
    and Keyword = PROGRAM 
              | VAR 
              | READ
              | WRITE
              | IF
              | THEN
              | ELSE
              | ENDIF
              | WHILE
              | DO
              | ENDWH
              | TT
              | FF
```
## Acknowledgements 
- Mainly for compiler.sml, glue.sml and examples related to .lex and .yacc
- UG.pdf    (http://rogerprice.org/ug/ug.pdf)
- compiler.sml is seen from compiler.sml in Figure 14 in http://rogerprice.org/ug/ug.pdf
- glue.sml is seen from glue.sml in Figure 13 in http://rogerprice.org/ug/ug.pdf
- while.lex and while.yacc is also referred from http://rogerprice.org/ug/ug.pdf
- Hypernotes for grammer and AST
- https://www.cs.princeton.edu/~appel/modern/ml/ml-yacc/manual.html#section23
- https://www.smlnj.org/doc/ML-Lex/manual.html
- http://www.smlnj.org/doc/ML-Yacc/
