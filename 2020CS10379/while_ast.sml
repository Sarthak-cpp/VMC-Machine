use "stack.sml";
use "datatypes.sml";
use "memory.sml";
use "rational.sml";
CM.make "While.cm";

open AST;
Control.Print.printLength := 100;
Control.Print.printDepth := 100;
Control.Print.stringDepth := 100;

signature VMC = 
    sig
        val locC: AST.AST Stack.Stack ref;
        val locV: AST.AST Stack.Stack ref;
        val locM: Memory.memory ref;
        val assignMemory: AST list -> unit;
        val getVal: AST -> ration.rational;
        val postfix: AST -> unit;
        val interpreter: AST -> unit;
        val execute: AST -> unit;
        val toString: unit -> string * string * string;
end;

structure Vmc: VMC =
    struct
        (* Initialize Control Stack, Value Stack and Memory for storing variables value *)
        val C: AST.AST Stack.Stack = Stack.create();
        val V: AST.AST Stack.Stack = Stack.create();
        val M: Memory.memory = Memory.create();
        val locC = ref C;
        val locV = ref V;
        val locM = ref M;

        fun ASTtoString(AST.Variable(a)) = a
          | ASTtoString(AST.Num(a)) = BigInt.to_String(a)
          | ASTtoString(AST.Bool(a)) = if a then "tt" else "ff"
          | ASTtoString(AST.PROCESS) = "procedure"
          | ASTtoString(AST.EMPTY) = "EMPTY"
          | ASTtoString(AST.ASSIGNRAT) = "ASSIGNRAT"
          | ASTtoString(AST.ASSIGNINT) = "ASSIGNINT"
          | ASTtoString(AST.ASSIGNBOOL) = "ASSIGNBOOL"
          | ASTtoString(AST.READ) = "READ"
          | ASTtoString(AST.WRITE) = "WRITE"
          | ASTtoString(AST.IF) = "IF"
          | ASTtoString(AST.THEN) = "THEN"
          | ASTtoString(AST.ELSE) = "ELSE"
          | ASTtoString(AST.FI) = "FI"
          | ASTtoString(AST.WHILE) = "WHILE"
          | ASTtoString(AST.DO) = "DO"
          | ASTtoString(AST.OD) = "OD"
          | ASTtoString(AST.INT) = "INT"
          | ASTtoString(AST.RATIONAL) = "RATIONAL"
          | ASTtoString(AST.BOOL) = "BOOL"
          | ASTtoString(AST.ADD) = "ADD"
          | ASTtoString(AST.RATADD) = "RATADD"
          | ASTtoString(AST.SUB) = "SUB"
          | ASTtoString(AST.MULTIPLY) = "MULTIPLY"
          | ASTtoString(AST.DIVIDE) = "DIVIDE"
          | ASTtoString(AST.RATDIV) = "RATDIV"
          | ASTtoString(AST.MODULO) = "MODULO"
          | ASTtoString(AST.NOT) = "NOT"
          | ASTtoString(AST.OR) = "OR"
          | ASTtoString(AST.AND) = "AND"
          | ASTtoString(AST.LESSTHAN) = "LESSTHAN"
          | ASTtoString(AST.LESSTHANEQ) = "LESSTHANEQ"
          | ASTtoString(AST.GREATERTHAN) = "GREATERTHAN"
          | ASTtoString(AST.GREATERTHANEQ) = "GREATERTHANEQ"
          | ASTtoString(AST.EQUALS) = "EQUALS"
          | ASTtoString(AST.NOTEQUAL) = "NOTEQUAL"
          | ASTtoString(AST.NEG) = "NEG";

        fun toString() = (Stack.toString ASTtoString (!locV), Memory.toString(!locM), Stack.toString ASTtoString (!locC));

        (* Assign Memory assigns a location for a variable in memory *)
        fun assignMemory([]) = ()
        | assignMemory(x::tail) = (
            Memory.addVariable(x, !locM);
            assignMemory(tail)
        );

        (* It gets integer value out of variable searched from memory or from AST.Num or AST.Bool *)
        fun getVal(AST.Variable(x)) = Memory.getVal(AST.Variable(x), !locM)
        | getVal(AST.Rat(x)) = x
        | getVal(AST.Num(x)) = (x,[1])
        | getVal(AST.Bool(x)) = if x then ([1],[1]) else ([0],[1]);

        (* Postfix function convert AST into PostFix form and push in Contol Stack *)
        (* It also finds out and initializes variables *)
        fun postfix(AST.Program(a, (b, c))) = 
            let
                fun helper([]) = ()
                    | helper(x::tail) = (
                        helper(tail);
                        postfix(x);
                    );
                
                fun helper2([]) = ()
                    | helper2((u, v)::tail) = (
                        assignMemory(u);
                        helper2(tail)
                    );
            in
                (
                    helper2(b);
                    locC := Stack.push(AST.PROGRAM, !locC);
                    Stack.push(AST.DOLLAR,!locC)
                    helper(c)
                    
                )
            end
        
        (* Postfix form for AssignRat *)
        | postfix(AST.AssignRat(a,b)) = (
            locC := Stack.push(AST.ASSIGNRAT, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for AssignInt *)
        | postfix(AST.AssignInt(a, b)) = (
            locC := Stack.push(AST.ASSIGNINT, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for AssignBool *)
        | postfix(AST.AssignBool(a, b)) = (
            locC := Stack.push(AST.ASSIGNBOOL, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for Read *)
        | postfix(AST.Read(a)) = (
            locC := Stack.push(AST.READ, !locC);
            postfix(a)
        )

        (* Postfix form for Write *)
        | postfix(AST.Write(a)) = (
            locC := Stack.push(AST.WRITE, !locC);
            postfix(a)
        )

        | postfix(AST.Call(a)) = (
            locC := Stack.push(AST.CALL, !locC);
        )

        (* Postfix form for IfThenElse *)
        | postfix(AST.IfThenElse(a, b, c)) = 
                let
                    fun helper([]) = ()
                    | helper(x::tail) = (
                        helper(tail);
                        postfix(x)
                        );
                in (
            locC := Stack.push(AST.IF, !locC);
            postfix(a);
            locC := Stack.push(AST.THEN, !locC);
            helper(b);
            locC := Stack.push(AST.ELSE, !locC);
            helper(c);
            locC := Stack.push(AST.FI, !locC)
        )
        end

        (* Postfix form for WhileDo *)
        | postfix(AST.WhileDo(a, b)) = 
                let
                    fun helper([]) = ()
                    | helper(x::tail) = (
                        helper(tail);
                        postfix(x)
                        );
                in (
            locC := Stack.push(AST.WHILE, !locC);
            postfix(a);
            locC := Stack.push(AST.DO, !locC);
            helper(b);
            locC := Stack.push(AST.OD, !locC)
        )
        end

        (* Postfix form for Add *)
        | postfix(AST.Add(a, b)) = (
            locC := Stack.push(AST.ADD, !locC); 
            postfix(a); 
            postfix(b)
            )
        
        | postfix(AST.MakeRat(a)) = (
            locC := Stack.push(AST.MKRAT, !locC);
            postfix(a);
        )

        | postfix(AST.ShowDec(a)) = (
            locC := Stack.push(AST.SHOWDEC, !locC);
            postfix(a);
        )

        | postfix(AST.FromDec(a)) = (
            locC := Stack.push(AST.FROMDEC, !locC);
            postfix(a);
        )

        | postfix(AST.ShowRat(a)) = (
            locC := Stack.push(AST.SHOWRAT, !locC);
            postfix(a);
        )
        
        (* Postfix form for RatAdd *)
        | postfix(AST.RatAdd(a, b)) = (
            locC := Stack.push(AST.RATADD, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for Sub *)
        | postfix(AST.Sub(a, b)) = (
            locC := Stack.push(AST.SUB, !locC);
            postfix(a); 
            postfix(b)
            )

        | postfix(AST.RatSub(a, b)) = (
            locC := Stack.push(AST.RATSUB, !locC);
            postfix(a);
            postfix(b);
        )
        
        (* Postfix form for Multiply *)
        | postfix(AST.Multiply(a, b)) = (
            locC := Stack.push(AST.MULTIPLY, !locC); 
            postfix(a); 
            postfix(b)
            )
        
        | postfix(AST.RatMul(a, b)) = (
            locC := Stack.push(AST.RATMUL, !locC);
            postfix(a);
            postfix(b);
        )

        | postfix(AST.RatDiv(a, b)) = (
            locC := Stack.push(AST.RATDIV, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for Divide *)
        | postfix(AST.Divide(a, b)) = (
            locC := Stack.push(AST.DIVIDE, !locC); 
            postfix(a); 
            postfix(b)
            )

        (* Postfix form for Modulo *)
        | postfix(AST.Modulo(a, b)) = (
            locC := Stack.push(AST.MODULO, !locC); 
            postfix(a); 
            postfix(b)
            )

        (* Postfix form for Negation *)
        | postfix(AST.Neg(a)) = (
            locC := Stack.push(AST.NEG, !locC);
            postfix(a)
        )

        (* Postfix form for Or *)
        | postfix(AST.Or(a, b)) = (
            locC := Stack.push(AST.OR, !locC); 
            postfix(a); 
            postfix(b)
            )

        (* Postfix form for And *)
        | postfix(AST.And(a, b)) = (
            locC := Stack.push(AST.AND, !locC); 
            postfix(a); 
            postfix(b)
        )

        (* Postfix form for LessThan *)
        | postfix(AST.LessThan(a, b)) = (
            locC := Stack.push(AST.LESSTHAN, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for LessThanEq *)
        | postfix(AST.LessThanEq(a, b)) = (
            locC := Stack.push(AST.LESSTHANEQ, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for GreaterThan *)
        | postfix(AST.GreaterThan(a, b)) = (
            locC := Stack.push(AST.GREATERTHAN, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for GreaterThanEq *)
        | postfix(AST.GreaterThanEq(a, b)) = (
            locC := Stack.push(AST.GREATERTHANEQ, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for Equals *)
        | postfix(AST.Equals(a, b)) = (
            locC := Stack.push(AST.EQUALS, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for NotEquals *)
        | postfix(AST.NotEqual(a, b)) = (
            locC := Stack.push(AST.NOTEQUAL, !locC);
            postfix(a);
            postfix(b)
        )

        (* Postfix form for Not *)
        | postfix(AST.Not(a)) = (
            locC := Stack.push(AST.NOT, !locC);
            postfix(a)
        )

        (* Postfix form for Variable / Numeral / Boolean *)
        | postfix(other) = locC := Stack.push(other, !locC);

        (* Move function moves value from stack a to b till "till" *)
        fun move(a, b, till) = 
            if (Stack.top(!a) = till) then (b := Stack.push(Stack.top(!a), !b); a := Stack.pop(!a))
            else (b := Stack.push(Stack.top(!a), !b); a := Stack.pop(!a); move(a, b, till));

        (* Remove function removes value from stack a till "till" *)
        fun remove(a, till) = 
            if (Stack.top(!a) = till) then a := Stack.pop(!a)
            else (a := Stack.pop(!a); remove(a, till));

        (* Copy function copies value from stack a to b till "till" *)
        fun copy(a, b, till) = 
            let
                val tempStk: AST.AST Stack.Stack = Stack.create();
                val temp = ref tempStk;
                val top = Stack.top(!a);
                fun helper() = 
                    if (Stack.top(!a) = till) then (
                        b := Stack.push(Stack.top(!a), !b);
                        temp := Stack.push(Stack.top(!a), !temp);
                        a := Stack.pop(!a)
                    )
                    else (
                        b := Stack.push(Stack.top(!a), !b);
                        temp := Stack.push(Stack.top(!a), !temp);
                        a := Stack.pop(!a);
                        helper()
                    );
            in(
                helper();
                move(temp, a, top)
            )
            end;

        (* It interprets AST.ADD as it sees in control stack*)
        fun interpreter(AST.ADD) =
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val (e,temp) = ration.add(getVal(a),getVal(c));
                val f = Stack.push(AST.Num(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end
        
        | interpreter(AST.RATADD) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = ration.add(getVal(a),getVal(c));
                val f = Stack.push(AST.Rat(e), d);
            in
                (locV := f, locC := Stack.pop(!locC))
            end

        (* It interprets AST.SUB as it sees in control stack*)
        | interpreter(AST.SUB) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val (e,temp) = ration.subtract(getVal(a),getVal(c));
                val f = Stack.push(AST.Num(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end
        
        | interpreter(AST.RATSUB) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = ration.subtract(getVal(a),getVal(c));
                val f = Stack.push(AST.Rat(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.MULTIPLY as it sees in control stack*)
        | interpreter(AST.MULTIPLY) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val (e,temp) = ration.multiply(getVal(a), getVal(c));
                val f = Stack.push(AST.Num(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        | interpreter(AST.RATMUL) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = ration.multiply(getVal(a), getVal(c));
                val f = Stack.push(AST.Rat(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.DIVIDE as it sees in control stack*)
        | interpreter(AST.DIVIDE) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val (temp1, temp2) = getVal(a);
                val (temp3, temp4) = getVal(b);
                val e = BigInt.divide(temp1,temp3);
                val f = Stack.push(AST.Num(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        | interpreter(AST.RATDIV) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = ration.divide(getVal(a), getVal(c));
                val f = Stack.push(AST.Rat(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end
        (* It interprets AST.MODULO as it sees in control stack*)
        | interpreter(AST.MODULO) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val (temp1, temp2) = getVal(a);
                val (temp3, temp4) = getVal(b);
                val e = BigInt.MOD(temp1,temp3);
                val f = Stack.push(AST.Num(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.ASSIGNINT as it sees in control stack*)
        | interpreter(AST.ASSIGNINT) = 
            let
                val a = Stack.top(!locV);
                val b = locV := Stack.pop(!locV);
                val c = Stack.top(!locV);
                val d = Stack.pop(!locV);
                val e = Stack.pop(!locC);
            in
                (locC := e; locV := d; Memory.update(a, !locM, getVal(c)))
            end

        (* It interprets AST.ASSIGNBOOL as it sees in control stack*)
        | interpreter(AST.ASSIGNBOOL) = 
            let
                val a = Stack.top(!locV);
                val b = locV := Stack.pop(!locV);
                val c = Stack.top(!locV);
                val d = Stack.pop(!locV);
                val e = Stack.pop(!locC);
            in
                (locC := e; locV := d; Memory.update(a, !locM, getVal(c)))
            end
        
        | interpreter(AST.ASSIGNRAT) = 
            let
                val a = Stack.top(!locV);
                val b = locV := Stack.pop(!locV);
                val c = Stack.top(!locV);
                val d = Stack.pop(!locV);
                val e = Stack.pop(!locC);
            in
                (locC := e; locV := d; Memory.update(a, !locM, getVal(c)))
            end

        (* It interprets AST.READ as it sees in control stack*)
        | interpreter (AST.READ) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = TextIO.input TextIO.stdIn;
                val d = if(valOf(Int.fromString(c)) = NONE) then ration.fromDecimal(c)
                        else SOME(ration.rat(BigInt.fromString(c)));
                val e = Stack.pop(!locC);
            in
                (locC := e; locV := b; Memory.update(a, !locM, d))
            end

        (* It interprets AST.WRITE as it sees in control stack*)
        | interpreter (AST.WRITE) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Memory.getVal(a, !locM);
                val d = TextIO.output (TextIO.stdOut, Int.toString(c) ^ "\n");
                val e = Stack.pop(!locC);
            in
                (locC := e; locV := b)
            end

        (* It interprets AST.NOT as it sees in control stack*)
        | interpreter (AST.NOT) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = (getVal(a) = 0);
                val d = Stack.push(AST.Bool(c), b);
            in
                (locC := Stack.pop(!locC); locV := d)
            end

        (* It interprets AST.NEG as it sees in control stack*)
        | interpreter (AST.NEG) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = ration.neg(getVal(a));
                val (temp1, temp2) = c;
                if(temp2 == ration.one) then val d = Stack.push(AST.Num(c), b)
                else d = Stack.push(AST.Rat(c), b)
            in
                (locC := Stack.pop(!locC); locV := d)
            end

        (* It interprets AST.OR as it sees in control stack*)
        | interpreter (AST.OR) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) <> 0 orelse getVal(c) <> 0;
                val f = Stack.push(AST.Bool(e), d);
            in
                (locC := Stack.pop(!locC); locV := f)
            end

        (* It interprets AST.AND as it sees in control stack*)
        | interpreter (AST.AND) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) <> 0 andalso getVal(c) <> 0;
                val f = Stack.push(AST.Bool(e), d);
            in
                (locC := Stack.pop(!locC); locV := f)
            end

        (* It interprets AST.LESSTHAN as it sees in control stack*)
        | interpreter(AST.LESSTHAN) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) < getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.LESSTHANEQ as it sees in control stack*)
        | interpreter(AST.LESSTHANEQ) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) <= getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.GREATERTHAN as it sees in control stack*)
        | interpreter(AST.GREATERTHAN) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) > getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.GREATERTHANEQ as it sees in control stack*)
        | interpreter(AST.GREATERTHANEQ) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) >= getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.EQUALS as it sees in control stack*)
        | interpreter(AST.EQUALS) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) = getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.NOTEQUAL as it sees in control stack*)
        | interpreter(AST.NOTEQUAL) = 
            let
                val a = Stack.top(!locV);
                val b = Stack.pop(!locV);
                val c = Stack.top(b);
                val d = Stack.pop(b);
                val e = getVal(a) <> getVal(c);
                val f = Stack.push(AST.Bool(e), d);
            in 
                (locV := f; locC := Stack.pop(!locC))
            end

        (* It interprets AST.IF as it sees in control stack*)
        | interpreter(AST.IF) = 
            let
                val temp = locC := Stack.pop(!locC);
                val a = Stack.top(!locV);
                val b = locV := Stack.pop(!locV);
                val c = locV := Stack.pop(!locV);
            in
                if getVal(a) <> 0 then (
                    move(locV, locC, AST.ELSE);
                    locC := Stack.pop(!locC);
                    remove(locV, AST.FI)) 
                else (
                        remove(locV, AST.ELSE);
                        move(locV, locC, AST.FI);
                        locC := Stack.pop(!locC)
                    )
            end

        (* It interprets AST.FI as it sees in control stack*)
        | interpreter (AST.FI) = move(locC, locV, AST.THEN)

        | interpreter (AST.OD) = (
            move(locC, locV, AST.DO);
            copy(locC, locV, AST.WHILE)
        )

        (* It interprets AST.WHILE as it sees in control stack*)
        | interpreter (AST.WHILE) = 
            let 
                val a = Stack.top(!locV);
                val b = locV := Stack.pop(!locV);
                val c = locC := Stack.pop(!locC);
            in
                if (getVal(a) = 0) then (remove(locV, AST.OD))
                else (
                    move (locV, locC, AST.DO);
                    copy (locV, locC, AST.OD);
                    move (locV, locC, AST.OD);
                    locC := Stack.pop(!locC)
                )
            end

        | interpreter (other) = move(locC, locV, other);    

        (* It finally Evaluates the tree as it sees in control stack*)
        fun execute(Tree) = 
            let 
                val a = postfix(Tree);
                fun helper() = 
                    if Stack.empty(!locC) then ()
                    else (
                        interpreter(Stack.top(!locC));
                        helper()
                    );
            in
                helper()
            end;
end;
