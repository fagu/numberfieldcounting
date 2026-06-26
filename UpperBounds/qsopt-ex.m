// Wrapper for the QSopt_ex exact rational LP solver.

// Return (integer coefficient sequence, positive integer multiplier L).
function ClearDenominators(coeffs)
    L := Lcm([Denominator(c) : c in coeffs]);
    return [ Integers()!(c*L) : c in coeffs ], L;
end function;

// Format "+ a1 x1 - a2 x2 ..." from an integer coefficient sequence.
function LinExpr(coeffs)
    t := "";
    for j in [1..#coeffs] do
        c := coeffs[j];
        if c eq 0 then continue; end if;
        sgn := (c gt 0) select " + " else " - ";
        t := t cat sgn cat IntegerToString(Abs(c)) cat " x" cat IntegerToString(j);
    end for;
    if t eq "" then t := " 0"; end if;
    return t;
end function;

// Build a CPLEX-LP-format string with integer coefficients.
function BuildQSoptLP(LHS, rel, RHS, obj, direction)
	Qrat := Rationals();
	
	m := Nrows(LHS);
	n := Ncols(LHS);

    str := direction cat "\n";
	// Write the objective.
    objint := ClearDenominators([Qrat ! obj[1,j] : j in [1..n]]);
    str cat:= " " cat LinExpr(objint) cat "\n";
	// Write the conditions.
    str cat:= "Subject To\n";
    for i in [1..m] do
        rowAndRhs := [ Qrat ! LHS[i,j] : j in [1..n] ] cat [ Qrat ! RHS[i,1] ];
        ic := ClearDenominators(rowAndRhs);   // single positive scaling per row
        lhsint := [ ic[j] : j in [1..n] ];
        rhsint := ic[n+1];
        op := (rel[i,1] lt 0) select " <= "
              else ((rel[i,1] gt 0) select " >= " else " = ");
        str cat:= " " cat LinExpr(lhsint) cat op cat IntegerToString(rhsint) cat "\n";
    end for;
    str cat:= "End\n";
    return str;
end function;

function ParseRational(str)
	parts := Split(str, "/");
	if #parts eq 1 then
		return StringToInteger(parts[1]);
	elif #parts eq 2 then
		return StringToInteger(parts[1])/StringToInteger(parts[2]);
	else
		error "Unexpected number format.";
	end if;
end function;

function ParseQSoptSol(str, n)
	Qrat := Rationals();
	
	lines := Split(str);
	if lines[1] eq "status = OPTIMAL" then
		assert lines[2] eq "status OPTIMAL";
		assert Substring(lines[3], 1, 9) eq "\tValue = ";
		assert lines[4] eq "VARS:";
		sol := AssociativeArray();
		i := 1;
		while true do
			line := lines[4+i];
			if line eq "REDUCED COST:" then
				break;
			end if;
			parts := Split(line, "=");
			assert #parts eq 2;
			// Find out variable number.
			assert parts[1][1] eq "x" and parts[1][#parts[1]] eq " ";
			varnumber := StringToInteger(Substring(parts[1], 2, #parts[1]-2));
			assert varnumber ge 1 and varnumber le n;
			assert not IsDefined(sol, varnumber);
			// Find out value.
			assert parts[2][1] eq " ";
			val_str := Substring(parts[2], 2, #parts[2]-1);
			// Save the value.
			sol[varnumber] := ParseRational(val_str);
			// Go to next line.
			i +:= 1;
		end while;
		// Variables with value zero are not printed.
		for i in [1..n] do
			if not IsDefined(sol, i) then
				sol[i] := 0;
			end if;
		end for;
		sol := Matrix(Qrat, [[sol[i] : i in [1..n]]]);
		return sol, 0;
	elif lines[1] eq "status = INFEASIBLE" then
		return 0, 2;
	elif lines[1] eq "status = UNBOUNDED" then
		return 0, 3;
	else
		error "Unexpected status line:", lines[1];
	end if;
end function;

function QSoptOptimalSolution(LHS, rel, RHS, obj, direction)
	// Create a temporary directory for the lp problem.
	dirname := Pipe("mktemp -d -p " cat GetTempDir(), "");
	assert dirname[#dirname] eq "\n";
	dirname := Substring(dirname, 1, #dirname - 1) cat "/";
	infile := dirname cat "a.lp";
	outfile := dirname cat "a.sol";
	// Write the lp problem input file.
	input := BuildQSoptLP(LHS, rel, RHS, obj, "Maximize");
	Write(infile, input : Overwrite := true);
	// Call esolver.
	if System("esolver" cat " -O " cat outfile cat " " cat infile cat " 2> /dev/null") ne 0 then
		error "esolver returned non-zero exit code.";
	end if;
	// Read the solution file.
	sol, state := ParseQSoptSol(Read(outfile), NumberOfColumns(LHS));
	// Remove the temporary directory.
	System("rm " cat infile);
	System("rm " cat outfile);
	System("rm -d " cat dirname);
	return sol, state;
end function;

// This function behaves like MaximalSolution(...), but uses exact rational arithmetic.
function QSoptMaximalSolution(LHS, rel, RHS, obj)
	return QSoptOptimalSolution(LHS, rel, RHS, obj, "Maximize");
end function;

// This function behaves like MinimalSolution(...), but uses exact rational arithmetic.
function QSoptMinimalSolution(LHS, rel, RHS, obj)
	return QSoptOptimalSolution(LHS, rel, RHS, obj, "Minimize");
end function;
