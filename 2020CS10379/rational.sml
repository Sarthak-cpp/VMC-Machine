use "bigint.sml";
signature RATIONAL =
sig
    type rational = BigInt.bigint * BigInt.bigint
    exception rat_error
    val make_rat: BigInt.bigint * BigInt.bigint -> rational option
    val rat: BigInt.bigint -> rational option
    val reci: BigInt.bigint -> rational option
    val neg: rational -> rational
    val inverse : rational -> rational option
    val equal : rational * rational -> bool (* equality *)
    val less : rational * rational -> bool (* less than *)
    val add : rational * rational -> rational (* addition *)
    val subtract : rational * rational -> rational (* subtraction *)
    val multiply : rational * rational -> rational (* multiplication *)
    val divide : rational * rational -> rational option (* division *)
    val showRat : rational -> string
    val showDecimal : rational -> string
    val fromDecimal : string -> rational
    val toDecimal : rational -> string

end;

functor Rational(Big : BIGINT) : RATIONAL = 
struct
    type rational = BigInt.bigint * BigInt.bigint
    exception rat_error;
    val zero = [0]
    val one = [1]
    val minus_one = [~1]
    fun make_rat(x : BigInt.bigint, y : BigInt.bigint) = if(y = zero) then NONE
                                           else SOME (BigInt.get_coprime_pair(x,y))
    
    (* fun printList(x : BigInt.bigint list) = if(null x) then print("\n") else let val temp = print(BigInt.to_String(hd x) ^ " , " ) in printList(tl x) end; *)

    fun rat(x : BigInt.bigint) = SOME (x,one)
    fun reci(x : BigInt.bigint) = make_rat(one,x)
    fun neg(x : rational) = let val (a,b) = x
                                val (p,q) = valOf(make_rat(a, b))
                                in (BigInt.negate(p),q) end
    fun inverse(x : rational) = let val (a,b) = x
                                    in if(a = zero) then NONE else SOME (BigInt.get_coprime_pair(b,a)) end
    
    fun equal(x : rational, y : rational) = let val (a,b) = x
                                                val (p,q) = y
                                                val (a0,b0) = BigInt.get_coprime_pair(a,b)
                                                val (p0,q0) = BigInt.get_coprime_pair(p,q)
                                                in ((a0 = p0) andalso (b0 = q0)) end
    
    fun less(x : rational, y : rational) = let val (a,b) = x
                                               val (p,q) = y
                                               val (a0,b0) = BigInt.get_coprime_pair(a,b)
                                               val (p0,q0) = BigInt.get_coprime_pair(p,q)
                                               val temp = BigInt.subtract(BigInt.multiply(a0,q0),BigInt.multiply(p0,b0))
                                               in if(BigInt.less(temp,zero)) then true else false end
    
    fun add(x : rational, y : rational) = let val (a,b) = x
                                              val (p,q) = y
                                              in BigInt.get_coprime_pair(BigInt.add(BigInt.multiply(a,q), BigInt.multiply(b,p)), BigInt.multiply(b,q)) end
    
    fun subtract(x : rational, y : rational) = let val (a,b) = x
                                                   val (p,q) = y
                                                   in BigInt.get_coprime_pair(BigInt.subtract(BigInt.multiply(a,q), BigInt.multiply(b,p)), BigInt.multiply(b,q)) end

    fun multiply(x : rational, y : rational) = let val (a,b) = x
                                                   val (p,q) = y
                                                   in BigInt.get_coprime_pair(BigInt.multiply(a,p), BigInt.multiply(b,q)) end

    fun divide(x : rational, y : rational) = let val (a,b) = x
                                                 val (p,q) = y
                                                 in if(p = zero orelse b = zero) then NONE
                                                    else SOME (BigInt.get_coprime_pair(BigInt.multiply(a,q), BigInt.multiply(b,p))) end

    fun showRat(x : rational) = let val (a,b) = x
                                    val (p,q) = BigInt.get_coprime_pair(a,b)
                                    val str = BigInt.to_String(p) ^ "/" ^ BigInt.to_String(q)
                                    in str end

    fun get_pow_10(n : int) = if(n = 0) then [1] else get_pow_10(n-1)@[0];

    fun get_a(str : string) = let val L0 = explode(str)
                                  val L = tl L0
                                  fun helper(L : char list, a : BigInt.bigint) = if(hd L = #".") then a else helper(tl L, a@[valOf(Int.fromString(String.str(hd(L))))])
                                  in helper(L,[]) end
    
    fun get_b(str : string) = let val L0 = explode(str)
                                  val L = tl L0
                                  fun help1(L : char list) = if(hd L = #".") then tl L else help1(tl L)
                                  fun help2(L : char list, b : BigInt.bigint) = if(hd L = #"(") then b else help2(tl L, b @ [valOf(Int.fromString(String.str(hd(L))))])
                                  in help2(help1(L), []) end
    
    fun get_c(str : string) = let val L0 = explode(str)
                                  val L = tl L0
                                  fun help1(L : char list) = if(hd L = #"(") then tl L else help1(tl L)
                                  fun help2(L : char list, c : BigInt.bigint) = if(hd L = #")") then c else help2(tl L, c @ [valOf(Int.fromString(String.str(hd(L))))])
                                  in help2(help1(L), []) end
    
    fun fromDecimal(str : string) = let val a = get_a(str)
                                        val b = get_b(str)
                                        val c = get_c(str)
                                        val temp1 = a@b@c
                                        val temp2 = a@b
                                        val n = length(a)
                                        val k = length(b)
                                        val l = length(c)
                                        val num = BigInt.subtract(temp1,temp2)
                                        val den = BigInt.subtract(get_pow_10(k+l),get_pow_10(k))
                                        in if(c = []) then valOf(make_rat(a@b, get_pow_10(k))) else valOf(make_rat(num,den)) end;
    
    fun check_repeat(remainder_array : BigInt.bigint list, check_rem : BigInt.bigint, i : int) = if(null remainder_array) then ~1
                                                                                                 else if(hd remainder_array = check_rem) then i
                                                                                                 else check_repeat(tl remainder_array,check_rem,i+1)

    (* Recursive function takes in curr_a < b, appends 0 to curr_a, new_a = curr_a MOD b, if(check_rem(rem_arr,new_a,1)>0) then return (quo_arr,check_rem(rem_arr,new_a,1)) else insert curr_a/b in quo_arr, new_a in rem_arr and call function on new_a *)
    fun toDecHelper(rem_arr : BigInt.bigint list, quo_arr : BigInt.bigint list, curr_a : BigInt.bigint, b : BigInt.bigint) = 
        let val extend = curr_a@[0]
            val new_a = BigInt.MOD(extend,b)
        in if(new_a = zero) then (quo_arr@[BigInt.divide(extend,b)],~1)
           else let val idx = check_repeat(rem_arr,new_a,0)
                in if(idx >= 0) then (quo_arr@[BigInt.divide(extend,b)],idx)
                   else toDecHelper(rem_arr@[new_a], quo_arr@[BigInt.divide(extend,b)], new_a, b)
                end
        end

    fun get_N(quo_arr : BigInt.bigint list, idx : int) = if (null quo_arr) then ""
                                                       else if(idx < 0) then BigInt.to_String(hd quo_arr) ^ get_N(tl quo_arr, idx)
                                                       else if(idx = 0) then ""
                                                       else BigInt.to_String(hd quo_arr) ^ get_N(tl quo_arr, idx - 1)

    fun get_R(quo_arr : BigInt.bigint list, idx : int) = if(idx < 0) then ""
                                                         else if(null quo_arr) then ""
                                                         else let fun helper1(quo_arr : BigInt.bigint list, idx : int) = if(idx = 0) then quo_arr else helper1(tl quo_arr, idx - 1)
                                                              in get_N(helper1(quo_arr,idx),~1) end;

    fun toDecimal(x : rational) = let val (a,b) = x
                                      val (p0, q0) = BigInt.get_coprime_pair(a,b)
                                      val sign = if(hd p0 < 0) then "-" else "+"
                                      val p = BigInt.abs(p0)
                                      val q = BigInt.abs(q0)
                                      val I = BigInt.to_String(BigInt.divide(p,q))
                                      val dot = "."
                                      val LPAR = "("
                                      val RPAR = ")"
                                      val curr_a = BigInt.MOD(p,q)
                                      val (quo_arr, idx) = toDecHelper([curr_a], [], curr_a, q)
                                      val N = get_N(quo_arr, idx)
                                      val R = get_R(quo_arr, idx)
                                      in sign ^ I ^ dot ^ N ^ LPAR ^ R ^ RPAR end;

    fun showDecimal(x : rational) = toDecimal(x);
end;

structure ration = Rational(BigInt);