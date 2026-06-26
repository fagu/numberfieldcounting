// Code to determine whether one vector is \geq some vector in the convex hull of a bunch of others

function InConvexHullShadow(questionable_vec, baseline_vecs)
	/*
		Set up the linear programming problem as follows:
		We want to know whether questionable_vec is \geq some vector in the convex hull of the vectors in baseline_vecs
		Suppose the vectors have dimension D, and there are N vectors in baseline_vecs
		We will look for variables c1,...,cN such that:
			1) ci \geq 0 for each i
			2) c1 + ... + cN = 1
			3) c1 v1[i] + ... + cN vN[i] <= questionable_vec[i]
		This will be a total of N + 1 + D constraints.
	*/
	
	D := #questionable_vec;
	N := #baseline_vecs;
	
	// Magma does not like LP problems with zero variables, so we explicitly handle this trivial case.
	if N eq 0 then
		return false;
	end if;
	
	// Note that all variables are implicitly required to be >= 0 by the lp solvers,
	// so we do not need to explicitly impose non-negativity.
	
	// The constraint c_1 + ... + c_N = 1.
	ConvexConstraints := [[1 : i in [1..N]]];
	ConvexTargets := [1];
	// Magma codes relations by: (positive = \geq), (0 = equals), (negative = \leq)
	ConvexRelations := [0];
	
	ComparisonConstraints := [[baseline_vecs[i][j] : i in [1..N]] : j in [1..D]];
	ComparisonTargets := questionable_vec;
	ComparisonRelations := [-1 : i in [1..D]];
	
	Qrat := Rationals();
	
	ConstraintMatrix:=Matrix(Qrat, ConvexConstraints cat ComparisonConstraints);
	TargetMatrix:=Matrix(Qrat, [ConvexTargets cat ComparisonTargets]);
	RelationsMatrix:=Matrix(Qrat, [ConvexRelations cat ComparisonRelations]);
	
	ObjectiveMatrix := Matrix(Qrat, [[1 : i in [1..N]]]);
	
	Sol, state := QSoptMaximalSolution(
		ConstraintMatrix,
		Transpose(RelationsMatrix),
		Transpose(TargetMatrix),
		ObjectiveMatrix
	);
	if state eq 0 then
		return true;
	elif state eq 2 then
		//print state;
		return false;
	else
		print "Got strange result!  Please report.";
		return false;
	end if;
end function;

// Returns the corners of the Minkowski sum of the convex hull of the given vectors and the positive quadrant cone, or equivalently of the set of vectors that are entry-wise >= some vector in the convex hull of the given vectors.
function ConvexHullShadowGenerators(vecs)
	current_vecs := vecs;
	ind := 1;
	
	while ind le #current_vecs do
		pruned_set := current_vecs[1..ind-1] cat current_vecs[ind+1..#current_vecs];
		if InConvexHullShadow(current_vecs[ind], pruned_set) then
			Remove(~current_vecs, ind);
		else
			ind := ind+1;
		end if;
	end while;
	
	return current_vecs;
end function;
