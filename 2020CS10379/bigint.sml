signature BIGINT = 
sig
    type bigint = int list
    exception big_int_error

    val zero : bigint
    val one : bigint
    val minus_one : bigint
    val empt : bigint

    val fromInt : int -> bigint
    val fromString : string -> bigint
    val to_String : bigint -> string 
    val add : bigint * bigint -> bigint
    val subtract : bigint * bigint -> bigint
    val multiply : bigint * bigint -> bigint
    val divide : bigint * bigint -> bigint
    val gcd : bigint * bigint -> bigint
    val MOD : bigint * bigint -> bigint
    val less : bigint * bigint -> bool
    val negate : bigint -> bigint
    val abs : bigint -> bigint
    val get_coprime_pair : bigint * bigint -> bigint * bigint
    (* val divide_helper : bigint * bigint * bigint * bigint -> bigint *)
    (* val getNextDigit : bigint * bigint * int -> int *)
end;

structure BigInt : BIGINT =
struct
    type bigint = int list

    val zero = [0]

    val one = [1]

    val minus_one = [~1]
    
    val empt = []

    exception big_int_error;

    fun removeLeadingZeros L = if(null L) then [0] 
                               else if(hd L = 0) then removeLeadingZeros(tl L)
                               else L;

    fun fromInt(x : int) = if(x<0) then let val temp = fromInt(~x)
                                            val head = hd(temp)
                                            val res = [~head]@tl(temp)
                                            in res end
                            else if(x div 10 = 0) then [x]
                            else fromInt(x div 10)@[x mod 10];

    fun fromString(x : string) = let val L = explode(x);
                                    fun helper(L,L0) = if(null L) then L0 
                                                       else if((hd(L) < #"0" orelse hd(L) > #"9") andalso hd(L) <> #"~") then raise big_int_error
                                                       else if(hd(L) = #"~") then helper(tl(tl L),L0@[(~1)*valOf(Int.fromString(String.str(hd(tl L))))]) 
                                                       else helper(tl L, L0@[valOf(Int.fromString(String.str(hd(L))))] )
                                    in helper(L,[]) end;
    
    fun to_String(x : bigint) = if(null x) then "" else Int.toString(hd x)^to_String(tl x);
    
    fun negate(x0 : bigint) = let val x = removeLeadingZeros(x0)
                                in [~(hd x)]@tl(x) end

    fun abs(x0 : bigint) = let val x = removeLeadingZeros(x0)
                                in if(hd x >= 0) then x else [~(hd x)]@tl(x) end;

    fun less(x0 : bigint, y0 : bigint) = let val x = removeLeadingZeros(x0)
                                             val y = removeLeadingZeros(y0)
                                             in if(x = y) then false
                                                else if(hd x < 0 andalso hd y > 0) then true
                                                else if(hd x > 0 andalso hd y < 0) then false    
                                                else if(hd x < 0 andalso hd y < 0) then if(less(negate(x),negate(y))) then false else true 
                                                else if(length x > length y) then false
                                                else if(length x < length y) then true
                                                else if(hd x > hd y) then false else if(hd x < hd y) then true
                                                else less(tl x, tl y)
                                             end

    fun add(x0 : bigint , y0 : bigint) = let val x = removeLeadingZeros(x0)
                                             val y = removeLeadingZeros(y0)
                                             in if(hd x > 0 andalso hd y < 0) then subtract(x, negate(y))
                                                else if(hd x < 0 andalso hd y > 0) then subtract(y, negate(x))
                                                else if(hd x < 0 andalso hd y < 0) then negate(add(negate(x), negate(y)))
                                                else let val L1 = rev(x)
                                                         val L2 = rev(y)
                                                         fun addHelper(L1 : bigint, L2 : bigint, carry : int) =  if(null L1 andalso null L2) then [carry]
                                                                                                                 else if(null L1) then let val temp = ((hd L2) + carry) mod 10;
                                                                                                                                       in [temp]@addHelper(L1, tl(L2), (hd(L2) + carry) div 10) end
                                                                                                                 else if(null L2) then addHelper(L2, L1, carry)
                                                                                                                 else let val temp = (hd L1 + hd L2 + carry) mod 10
                                                                                                                         in [temp]@addHelper(tl L1, tl L2, (hd L1 + hd L2 + carry) div 10) end
                                                     in removeLeadingZeros(rev(addHelper(L1,L2,0))) end
                                             end

    and subtract(x0 : bigint, y0 : bigint) = let val x = removeLeadingZeros(x0)
                                                 val y = removeLeadingZeros(y0)
                                                 in if(hd x > 0 andalso hd y < 0) then add(x, negate(y))
                                                    else if(hd x < 0 andalso hd y > 0) then negate(add(negate(x), y))
                                                    else if(hd x < 0 andalso hd y < 0) then subtract(negate(y), negate(x))
                                                    else if(less(x,y)) then negate(subtract(y,x))
                                                    else let val L1 = rev(x)
                                                             val L2 = rev(y)
                                                             fun subHelper(L1 : bigint, L2 : bigint, carry : int) =  if(null L1 andalso null L2) then []
                                                                                                                     else if(null L2) then if(hd L1 = 0 andalso carry > 0) then [9]@subHelper(tl L1, L2, 1)
                                                                                                                                           else [hd(L1) - carry]@subHelper(tl L1, L2, 0)
                                                                                                                     else if(hd(L1) - hd(L2) - carry >= 0) then [hd(L1) - hd(L2) - carry]@subHelper(tl L1, tl L2, 0)
                                                                                                                     else [10 + hd(L1) - hd(L2) - carry]@subHelper(tl L1, tl L2, 1)
                                                         in removeLeadingZeros(rev(subHelper(L1,L2,0))) end
                                                 end;
    
    fun multiply(x0 : bigint, y0 : bigint) = let val x = removeLeadingZeros(x0)
                                                 val y = removeLeadingZeros(y0)
                                                 in if(x = zero orelse y = zero) then zero
                                                    else if(hd x < 0 andalso hd y < 0) then multiply(negate(x),negate(y))
                                                    else if(hd x * hd y < 0) then negate(multiply(abs(x),abs(y)))
                                                    else   let fun multiply_with_digit(x : bigint, d : int) =  let val L = rev(x)
                                                                                                                   fun helper(L,carry) = if(null L) then [carry]
                                                                                                                                         else [(d*(hd L) + carry) mod 10]@helper(tl L, (d*(hd L) + carry) div 10)
                                                                                                               in removeLeadingZeros(rev(helper(L,0))) end
                                                               fun addEndingZeros(x : bigint, k : int) = if(k = 0) then x else addEndingZeros(x,k-1)@[0]
                                                               val b = rev(y)
                                                               fun mult_helper(x : bigint, b : bigint, res : bigint, i : int) = if(null b) then res
                                                                                                                                else let val temp = addEndingZeros(multiply_with_digit(x, hd b),i)
                                                                                                                                     in mult_helper(x, tl b, add(temp,res),i+1) end
                                                           in mult_helper(x,b,zero,0) end
                                                 end;

    fun getNextDigit(a : bigint, b : bigint, i : int) = let val a0 = removeLeadingZeros(a)
                                                            val b0 = removeLeadingZeros(b) 
                                                            in  if(less(a0, multiply(b0, [i]))) then (i-1) 
                                                                else getNextDigit(a0,b0,i+1) end

    fun divide_helper(curr_rem : bigint, a_left : bigint, b : bigint, curr_quotient : bigint) = if(null a_left) then if(less(curr_rem,b)) then removeLeadingZeros(curr_quotient) 
                                                                                                                     else removeLeadingZeros(curr_quotient@[getNextDigit(curr_rem,b,0)])
                                                                                                else let val temp = getNextDigit(curr_rem@[hd a_left],b,0) in divide_helper(subtract(curr_rem @ [hd a_left], multiply(b,[temp])), tl a_left, b, curr_quotient@[temp]) end 

    fun divide(a0 : bigint, b0 : bigint) = let val a = removeLeadingZeros(a0)
                                               val b = removeLeadingZeros(b0)
                                               in if(less(a,b)) then zero
                                                  else if(a = b) then one
                                                  else divide_helper([0],a,b,[0])
                                                                                                                                                       (* else if(less(curr_rem, b)) then divide_helper(removeLeadingZeros(curr_rem@[hd a_left]), tl a_left, b, removeLeadingZeros(curr_quotient@[0]))
                                                                                                                                                       else let val temp = getNextDigit(curr_rem, b, 0) in divide_helper(subtract(curr_rem, multiply(b, [temp])),tl a_left, b, curr_quotient@[temp]) end *)                                                         
                                               end;

    fun MOD(a0 : bigint, b0 : bigint) = let val a = removeLeadingZeros(a0)
                                            val b = removeLeadingZeros(b0)
                                            in subtract(a,multiply(b,divide(a,b))) end;

    fun gcd(a0 : bigint, b0 : bigint) = let val a = removeLeadingZeros(a0)
                                            val b = removeLeadingZeros(b0)
                                            in if(less(b,a)) then gcd(b,a)
                                               else if(a = zero) then b 
                                               else gcd(MOD(b,a),a)
                                            end
    

    fun get_coprime_pair(p0 : bigint, q0 : bigint) = let val p = removeLeadingZeros(p0)
                                                         val q = removeLeadingZeros(q0)
                                                         in if(p = zero) then (zero,one) 
                                                            else let val temp = gcd(abs(p),abs(q))
                                                                 in if((less(p,zero) andalso less(q,zero)) orelse (less(zero,p) andalso less(zero,q))) then (divide(abs(p), temp), divide(abs(q), temp))
                                                                    else (negate(divide(abs(p), temp)), divide(abs(q), temp)) end
                                                         end;

end;