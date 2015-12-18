(*Define lambda expression type*)
datatype Lambdaexp = V of int
| C of int
| App of Lambdaexp * Lambdaexp
| Abs of int * Lambdaexp

(*Find if an item is in the list*)
fun member (x, []) = false
| member (x, b::y) = if x = b then true else member(x, y)

(*Union two list/set*)
fun union ([], y) = y
| union (x::xs, ys) = if member(x, ys) then union(xs, ys) else x::union(xs, ys)

(*Delete an item from the list*)
fun delete (x, []) = []
| delete (x, y::ys) = if x = y then ys
                      else y::delete(x, ys)

(*Find the greater int from two*)
fun max (x:int, y:int) = if x < y then y else x

(*Find all free variables from a lambda expression*)
fun fv (V x) = [x]
| fv (App(y, z)) = union(fv(y), fv(z))
| fv (Abs(n, z)) = delete(n, fv(z))

(*Determine the index of a variable in form of integer*)
fun lindex (V n) = n
| lindex (App(x, y)) = max(lindex(x), lindex(y))
| lindex (Abs(n, z)) = max(n, lindex(z))

(*Determine if a lambda expression is in normal form*)
fun nf (V m) = true
| nf (Abs(n, z)) = nf(z)
| nf (App(Abs(n, x), y)) = false
| nf (App(x, y)) = nf(x) andalso nf(y)

(*Replace a variable in a lambda expression with another variable*)
fun repvar m n (V k) = if m = k then (V n) else (V k)
| repvar m n (App(x, y)) = App(repvar m n x, repvar m n y)
| repvar m n (Abs(k, z)) = if m = k then Abs(k, z) 
                           else if n = k then let val u = lindex(Abs(k, z)) + 1
                             in Abs(u, repvar m n (repvar n u z)) end
                           else Abs(k, repvar m n z)

(*Replace a veriable in a lambda expression with another lamber expression*)
fun repterm m y (V k) = if m = k then y else (V k)
| repterm m y (App(x, z)) = App(repterm m y x, repterm m y z)
| repterm m y (Abs(k, z)) = if m = k then Abs(k, z)
                            else Abs(k, repterm m y z)


(*Normalize a lambda expression*)
fun normalize (V n) = (V n)
| normalize (Abs(n, x)) = if nf(Abs(n, x)) then Abs(n, x)
                            else (Abs(n, normalize(x)))
| normalize (App((V n), (V m))) = App((V n), (V m))

| normalize (App((V n), x)) = if nf( (App((V n), x)) ) then App((V n), x)
                              else normalize(App((V n), normalize(x)))
| normalize (App(Abs(n, x), (V m))) = if nf(x) then normalize(repvar n m x)
                                      else normalize( (App(Abs(n, normalize(x)), (V m))) )
| normalize (App(Abs(n, x), y)) = if nf(x) then
                                     if member(n, fv(x)) then normalize(repterm n y x)
                                     else x
                                  else normalize( (App(Abs(n, normalize(x)), y)) )
| normalize (App(x, y)) = if nf((App(x, y))) then App(x, y)
                          else normalize( (App(normalize(x), normalize(y))) )

