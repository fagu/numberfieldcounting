/* The main program is euler.  It inputs a permutation group G and returns the associated Euler factor 
for all p, with x representing 1/p^a.  When G has a rational character the format of the output is 
[<[1],(desired Euler factor)>].  In general the format is represented by the output of 
euler(AlternatingGroup(8)) which is 

[
    <[ 1 ], 2*x^6 + 5*x^4 + 2*x^2 + 1>,
    <[ 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], 2*x^6>,
    <[ 1, 1, 0, 1, 0, 0, 0 ], 2*x^6>
]

The source of second line is the classes with cycle type (5,3).  They are switched by Gal(Q(Sqrt[-15])/2).  
The source of the third line is the classes with cycle type (7,1).  They are switched by 
Gal(Q(Sqrt[-7])/2.  The Euler factor, as a polynomial in x, at a prime p>7 depends only on the
two Jacobi symbols (-15/p) and (-7/p).  It is coded instead by the class of p modulo 7*15=105.  
For example to get the factor for p = 29 take the 29th element of each list, after wrapping, 
thus the 1st, 14th, and 1st list, thus 1, 0, and 1.  Use these as coefficients so that the final
polynomial is 1*(2*x^6 + 5*x^4 + 2*x^2 + 1)+0*(2*x^6)+1*(2*x^6) = 4*x^6 + 5*x^4 + 2*x^2 + 1
*/

/* Periodic functions f(k) on Z are represented by values on {1,...,n} where n is the exact period.  
Complications corresponding to zeroout and almostagree are there because we only care about values
f(k) with k relatively prime to n.  */

zeroout := function(L,d)
   return [(GCD(i,d)) eq 1 select  L[i] else 0: i in [1..#L]];
end function;

almostagree := function(big,small)
    inflate := &cat[small: i in [1..#big div #small]];
    return zeroout(big,#big) eq zeroout(inflate,#big);
end function;
 
period := function(L)
    n := #L;
    for p in [1..n] do
        if n mod p eq 0 then
            if almostagree(L,[L[i] : i in [1..p]]) then
                return p;
            end if;
        end if;
    end for;
    return n; // Fallback: the period is the entire list length
end function;

shorten := function(L)
   return [L[i]:i in [1..period(L)]];
end function;

consolidate := function(bilis)
   firsts := {x[1]:x in bilis};
   return [<f,&+[x[2]:x in bilis|x[1] eq f]>: f in firsts];
end function;

euler := function(G)
   C := ConjugacyClasses(G);
   P := PowerMap(G);
   d := Degree(G);
   powerdatalong := [[P(i,j): j in
   [k:k in [1..C[i][1]]/* |GCD(k,C[i][1]) eq 1 */]]:i in [1..#C]];
   powerdata := [shorten(p):p in powerdatalong];
   powerdata2 := 
   [ [ GCD(j,#powerdata[i]) gt 1 select 0 
   /* another symbol besides 0 would be an option, 
   to indicate that these 0's come just because j 
   is not coprime to the period */
   else (powerdata[i][j] eq powerdata[i][1] select 1 else 0) : 
   j in [1..#powerdata[i]]] :
    i in [1..#C]];
   return
   consolidate([<powerdata2[i],x^(d-#CycleDecomposition(C[i][3]))>: i in [1..#C]]);
end function;

weyl := function(s)  /*  "B4","D6", and "E8" are possible inputs */
    return StandardActionGroup(CoxeterGroup(s));
end function;

/*weyl gives easy access to interesting examples with rational character table, including some like 
weyl("E8") which are not accessible by TransitiveGroup(n,j) */



