// Usage: parallel -j128 -a gal_labels.txt magma -b label:={1} malle_basic.m

AttachSpec("FiniteGroups/Code/spec");
SetColumns(0);
//SetDebugOnError(true);

function makedivs(v, C, cm)
    // v is a set of integers, indexing into C
    // C = ConjugacyClasses(G)
    // cm = ClassMap(G)
    if #v eq 1 then return [v]; end if;
    divs := [];
    while #v gt 0 do
        r := Rep(v);
        newdiv := {r};
        Exclude(~v, r);
        for j:=1 to C[r][1]-1 do
            if GCD(j, C[r][1]) eq 1 then
                c := cm(C[r][3]^j);
                Include(~newdiv, c);
                Exclude(~v, c);
            end if;
            if #v eq 0 then break; end if;
        end for;
        Append(~divs, newdiv);
    end while;
    return divs;
end function;

function MinimalDivisions(G, C, ainv, inds)
    cm := ClassMap(G);
    // Step 1 partitions the classes based on the order of a generator
    // and the size of the class
    by_ordsize := AssociativeArray();
    for j:= 1 to #C do
	if inds[j] ne ainv then
	    continue;
	end if;
        c := C[j];
        os := [c[1], c[2]];
        if IsDefined(by_ordsize, os) then
            Include(~by_ordsize[os], j);
        else
            by_ordsize[os] := {j};
        end if;
    end for;
    // Separate a set of classes into divisions
    // The order of a rep is cc[r][1].  This could be more efficient
    // if we used generators for (Z/nZ)^* where n=cc[r][1]
    divisions := [];
    for os in Sort([k : k in Keys(by_ordsize)]) do
        for division in makedivs(by_ordsize[os], C, cm) do
            Append(~divisions, <os[1], os[2], division>);
        end for;
    end for;
    return divisions;
end function;

n, t := Explode([StringToInteger(c) : c in Split(label, "T")]);
G := TransitiveGroup(n, t);
if label eq "1T1" then
    ainv := 0;
    b := 0;
    concentrated_core := G;
    concentrated := "f";
    semiconcentrated := [];
    semiconcentrated := "f";
    d := 0;
    mdivs := [];
else
    cc := ConjugacyClasses(G);
    ind := [n - &+[pair[2] : pair in CycleStructure(c[3])] : c in cc[2..#cc]];
    ainv := Min(ind);
    mdivs := MinimalDivisions(G, cc, ainv, [0] cat ind);
    b := #mdivs;
    mdivs := [<c[1], c[2], #c[3], cc[Rep(c[3])][3]> : c in mdivs];
    concentrated_core := NormalClosure(G, sub<G | [c[4] : c in mdivs]>);
    semiconcentrated_cores := [NormalClosure(G, sub<G | c[4]>) : c in mdivs];
    concentrated := (#concentrated_core lt #G) select "t" else "f";
    semiconcentrated := &and[#core lt #G : core in semiconcentrated_cores] select "t" else "f";
    d := LCM([c[1] : c in mdivs]);
    mdivs := [Sprintf("%o|%o|%o|%o|%o", c[1], c[2], c[3], SaveElt(c[4]), Join([SaveElt(g) : g in GeneratorsSequence(S)], ",")) where c := mdivs[i] where S := semiconcentrated_cores[i] : i in [1..#mdivs]];
end if;
//print ainv;
//PrintFile(Sprintf("malle_a_out/%o", label), ainv);
PrintFile(Sprintf("malle_out/%o", label), Sprintf("%o|%o|%o|%o|%o|%o", ainv, b, d, concentrated, semiconcentrated, Join([SaveElt(g) : g in GeneratorsSequence(concentrated_core)], ",")));
PrintFile(Sprintf("malle_cc_out/%o", label), Join(mdivs, "\n"));
quit;
