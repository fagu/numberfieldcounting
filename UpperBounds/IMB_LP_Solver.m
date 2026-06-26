/*
	Code to compute an upper bound for a given inertial height function using a list of available inertial multiplicity bounds.  This follows the linear programming strategy suggested in RJLO's notes.
	
	Initial version created May 20, 2026, by Robert Lemke Oliver.
*/


function InertialUB_from_IMBs( weight, bounds : rational:=false, approx:=10^(-10))
	/* 
		Input:
			The weight of the target inertial height function.  This should be indexed by the conjugacy classes of nontrivial cyclic subgroups of a group G.
			A known list of inertial multiplicity bounds.
			Optionally: a boolean (rational) that indicates whether you expect the output to be rational
		Output:
			An upper bound on the number of fields ordered by the provided inertial height function.
	*/
	
	N := #weight;
	
	// We maximize k
	// among all choices of variables (e_1,...,e_N,k)
	// subject to the following constraints:
	//   e_i >= 0 for all i
	//   k >= 0
	//   \sum_i e_i weight[i] <= 1   (simplex constraint)
	//   k <= \sum_i e_i bounds[j][i] for all j   (imb constraint)
	
	// Note that all variables are implicitly required to be >= 0 by the lp solvers,
	// so we do not need to explicitly impose non-negativity.
	
	// Simplex constraints first
	SimplexConstraints := [weight cat [0]];
	SimplexTargets := [[1]];
	SimplexRelations := [[-1]];
	
	IMBConstraints := [bound cat [-1] : bound in bounds];
	IMBTargets := [[0] : bound in bounds];
	IMBRelations := [[1] : bound in bounds];
	
	Objective := [0 : i in [1..N]] cat [1];
	
	sol, state := MaximalSolution(
		Matrix(Qrat, SimplexConstraints cat IMBConstraints),
		Matrix(Qrat, SimplexRelations cat IMBRelations),
		Matrix(Qrat, SimplexTargets cat IMBTargets),
		Matrix(Qrat, [Objective])
	);
	
	// The problem is always feasible and bounded.
	assert state eq 0;
	
	k := sol[1,N+1];
	
	if rational eq false then
		return k;
	end if;
	
	i:=1;
	CFV := ContinuedFractionValue(ContinuedFraction(k : Bound:=1));
	while Abs(k - CFV) gt approx do
		i:=i+1;
		CFV := ContinuedFractionValue(ContinuedFraction(k : Bound:=i));
	end while;
	
	return CFV;
	
end function;
