signature STACK =
    sig
        type 'a Stack;
        exception EmptyStack;
        exception Error of string;
        val create: unit -> 'a Stack;
        val push : 'a * 'a Stack -> 'a Stack;
        val pop : 'a Stack -> 'a Stack;
        val top : 'a Stack -> 'a;
        val empty: 'a Stack -> bool;
        val poptop : 'a Stack -> ('a * 'a Stack) option;
        val nth : 'a Stack * int -> 'a;
        val drop : 'a Stack * int -> 'a Stack;
        val depth : 'a Stack -> int;
        val app : ('a -> unit) -> 'a Stack -> unit;
        val map : ('a -> 'b) -> 'a Stack -> 'b Stack;
        val mapPartial : ('a -> 'b option) -> 'a Stack -> 'b Stack;
        val find : ('a -> bool) -> 'a Stack -> 'a option;
        val filter : ('a -> bool) -> 'a Stack -> 'a Stack;
        val foldr : ('a * 'b -> 'b) -> 'b -> 'a Stack -> 'b;
        val foldl : ('a * 'b -> 'b) -> 'b -> 'a Stack -> 'b;
        val exists : ('a -> bool) -> 'a Stack -> bool;
        val all : ('a -> bool) -> 'a Stack -> bool;
        val list2Stack : 'a list -> 'a Stack; (*Convert a list into a Stack*)
        val Stack2list: 'a Stack -> 'a list; (*Convert a Stack into a list*)
        val toString: ('a -> string) -> 'a Stack -> string;
end;

structure Stack: STACK = 
    struct
        type 'a Stack = 'a list;
        exception EmptyStack;
        exception Error of string;
        fun create () = [];

        (* fun push (x, stk) = x::stk; *)
        fun push(x, []) = [x]
          | push(x, stk) = x::stk;

        fun pop [] = raise EmptyStack
          | pop (x::tail) = tail;
        
        fun top [] = raise EmptyStack
          | top (x::tail) = x;

        fun empty [] = true
          | empty (stk) = false;

        fun poptop [] = NONE
          | poptop (x::tail) = SOME (x, tail);

        fun depth stk = 
            let
                fun helper ([], n) = n
                  | helper (x::tail, n) = helper(tail, n + 1);
            in
                helper (stk, 0)
            end;
        
        fun nth (stk, n) = 
            if n < 0 orelse n >= depth stk then raise Error("Index out of Range")
            else
                let        
                    fun helper (stk, n) = 
                        if n = 0 then hd stk
                        else helper (tl stk, n - 1);
                in
                    helper (stk, n)
                end;
        
        fun drop (stk, n) = 
            if n < 0 orelse n > depth stk then raise Error("Drop size out of Range")
            else
                let
                    fun helper (stk, n) = 
                        if n = 0 then stk
                        else helper (tl stk, n - 1);
                in 
                    helper (stk, n)
                end;

        fun app f stk = List.app f stk;

        fun map f [] = []
          | map f (x::tail) = (f x)::(map f tail);
        
        fun mapPartial f [] = []
          | mapPartial f (x::stk) = 
                if isSome (f x) then (valOf (f x))::(mapPartial f stk)
                else mapPartial f stk;
        
        fun find f [] = NONE
          | find f (x::tail) = 
                if f x then SOME x
                else find f tail;
        
        fun filter f [] = []
          | filter f (x::tail) = 
                if f x then x::(filter f tail)
                else filter f tail;

        fun foldl f init [] = init 
          | foldl f init (x::tail) = foldl f (f(x, init)) tail;
        
        fun foldr f init [] = init
          | foldr f init (x::tail) = f (x, foldr f init tail);
        
        fun exists f [] = false
          | exists f (x::tail) = 
                if f x then true
                else exists f tail;
        
        fun all f [] = true
          | all f (x::tail) = 
                if f x then all f tail
                else false;
        
        fun list2Stack stk = stk;
        fun Stack2list list = list;

        fun toString f [] = ""
          | toString f (x::tail) = (f x) ^ (toString f tail);
end;