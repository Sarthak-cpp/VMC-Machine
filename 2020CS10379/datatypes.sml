use "rational.sml";
structure AST = 
    struct 
        datatype AST = Program of ((AST list *  AST list * AST list) * AST list) * AST list
                    | Procdeff of AST * (((AST list *  AST list * AST list) * AST list) * AST list)
                    | AssignRat of AST * AST
                    | AssignBool of AST * AST
                    | AssignInt of AST * AST
                    | Read of AST
                    | Write of AST
                    | Call of AST
                    | IfThenElse of AST * AST list * AST list
                    | WhileDo of AST * AST list
                    | Add of AST * AST
                    | MakeRat of AST
                    | ShowRat of AST
                    | ShowDec of AST
                    | FromDec of string
                    | ToDec of AST
                    | RatAdd of AST * AST
                    | Sub of AST * AST
                    | RatSub of AST * AST
                    | Multiply of AST * AST
                    | RatMul of AST * AST
                    | Divide of AST * AST
                    | RatDiv of AST * AST
                    | Modulo of AST * AST
                    | Num of BigInt.bigint
                    | Rat of string
                    | Neg of AST
                    | IntExpInPar of AST
                    | Or of AST * AST
                    | And of AST * AST
                    | Bool of bool
                    | Comp of AST
                    | BoolExpInPar of AST
                    | Not of AST
                    | LessThan of AST * AST
                    | LessThanEq of AST * AST
                    | GreaterThan of AST * AST
                    | GreaterThanEq of AST * AST
                    | Equals of AST * AST
                    | NotEqual of AST * AST
                    | Variable of string
                    | Identifier of string
                    | DecimalForm of string
                    | RationalForm of string
                    | COMSEQ of AST list
                    | EMPTY
                    | PROCESS
                    | ASSIGNRAT
                    | ASSIGNINT
                    | ASSIGNBOOL
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
                    | INT
                    | BIGINT
                    | RATIONAL
                    | RAT
                    | BOOL
                    | ADD
                    | RATADD
                    | SUB
                    | RATSUB
                    | MULTIPLY
                    | RATMUL
                    | DIVIDE
                    | RATDIV
                    | RATDECFORM
                    | MODULO
                    | NOT
                    | OR
                    | AND
                    | LESSTHAN
                    | LESSTHANEQ
                    | GREATERTHAN
                    | GREATERTHANEQ
                    | EQUALS
                    | DOLLAR
                    | NOTEQUAL
                    | NEG
                    | MKRAT
                    | SHOWDEC
                    | SHOWRAT
                    | FROMDEC
                    | TODEC
end;