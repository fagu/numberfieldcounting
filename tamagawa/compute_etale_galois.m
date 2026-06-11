// Run this after generating etale algebras up to some degree using etale_generation.py

// Usage: parallel -j 8 -a gal_todo.txt magma -b label:={1} compute_etale_galois.m

SetColumns(0);
AttachSpec("pAdicGaloisGroup/spec");
AttachSpec("ExactpAdics2/spec");
AttachSpec("../FiniteGroups/Code/spec");
PGG_UseExactpAdicsRoots();
PGG_UseExactpAdicsFactorization();

p := StringToInteger(Split(label, ".")[1]);
//K := ExactpAdicField(p);
K := pAdicField(2, 100);
R<x> := PolynomialRing(K);
poly := eval Read("etale_polys/" * label);
G := PGG_GaloisGroup(poly);
PrintFile("etale_gals/" * label, GroupToString(G : use_id:=false));
quit;
