use "datatypes.sml";
use "rational.sml";

signature MEMORY = 
    sig
        type memory = (AST.AST * ration.rational) Array.array;
        val create: unit -> memory;
        val getIndex: (AST.AST * memory) -> int;
        val addVariable: AST.AST * memory -> unit;
        val getVal: AST.AST * memory -> ration.rational;
        val update: AST.AST * memory * ration.rational -> unit;
        val toString: memory -> string;
end;

structure Memory: MEMORY = 
    struct
        type memory = (AST.AST * ration.rational) Array.array;
        fun create() = Array.array(1000, (AST.EMPTY, ([0],[1])));

        fun toString(mem) = 
            let fun helper (i) = 
                if i = 1000 then ""
                else let val (u, v) = Array.sub(mem, i);
                    in ration.showRat(v) ^ ", " ^ helper(i + 1)
                end;
            in helper 0
            end;

        fun getIndex(var, mem) = 
            let
                fun helper(var, mem, i) = 
                    let val (u, v) = Array.sub(mem, i);
                    in
                        if (u = var) then i
                        else if (u = AST.EMPTY) then ~1
                        else helper(var, mem, i + 1)
                end;
            in
                helper(var, mem, 0)
        end;

        fun addVariable(var : AST.AST, mem : memory) =
            let
                val i = getIndex(AST.EMPTY, mem);
            in
                Array.update(mem, i, (var, ([0],[1])))
        end;

        fun getVal(var : AST.AST , mem : memory) = 
            let
                val i = getIndex(var, mem);
                val (u, v) = Array.sub(mem, i);
            in
                v
        end;

        fun update(var, mem, newVal) = 
            let
                val i = getIndex(var, mem);
            in
                Array.update(mem, i, (var, newVal))
        end;
end;