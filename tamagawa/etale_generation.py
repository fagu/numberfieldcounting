#!/usr/bin/env -S sage -python

# Do ./etale_generation.py --help for some help
# Usage example (will populate gal_todo.txt, etale_gals, and etale_polys
# ./etale_generation.py -P 6 -N 6

import argparse
import sys
import os
import itertools
from itertools import combinations_with_replacement
from collections import Counter, defaultdict
from sage.all import Partitions, ZZ, PolynomialRing, LCM, flatten, prod, polygen, prime_range

opj = os.path.join

parser = argparse.ArgumentParser("etale_generation", description="This script generates etale algebras over Qp")
parser.add_argument("-p", "--prime", type=int, help="the residue characteristic")
parser.add_argument("-P", "--prime-bound", type=int, help="upper bound on residue characteristic")
parser.add_argument("-n", "--degree", type=int, help="the degree")
parser.add_argument("-N", "--degree-bound", type=int, help="upper bound on the degree")
parser.add_argument("-t", "--todofile", default="gal_todo.txt", help="location to save etale algebra labels where the Galois group needs to be computed")
parser.add_argument("-g", "--galfolder", default="etale_gals", help="folder in which to save Galois group output")
parser.add_argument("-f", "--polyfolder", default="etale_polys", help="folder in which to save separable polynomials defining the etale algebras")

def make_dictionaries(p, nbound, Gbound=None):
    sys.path.append("../lmfdb")
    from lmfdb import db
    gal_size = {rec["label"]: rec["order"] for rec in db.gps_transitive.search({"n":{"$lte":nbound}}, ["label", "order"])}
    R = PolynomialRing(ZZ, 'x')
    poly_lookup = {}
    gal_lookup = {}
    by_n = defaultdict(list)
    for rec in db.lf_fields.search({"p": p, "n": {"$lte": nbound}}, ["new_label", "coeffs", "n", "galois_label"]):
        if Gbound is None or gal_size[rec["galois_label"]] <= Gbound(rec["n"]):
            poly_lookup[rec["new_label"]] = R(rec["coeffs"])
            gal_lookup[rec["new_label"]] = rec["galois_label"]
            by_n[rec["n"]].append(rec["new_label"])
    return gal_size, poly_lookup, gal_lookup, by_n

def make_etale(p, n, Gbound=None, gal_size=None, poly_lookup=None, gal_lookup=None, by_n=None):
    assert ZZ(p).is_prime() and p < 200 and n in ZZ and 0 < n < 24
    x = polygen(ZZ, "x")
    if gal_size is None or poly_lookup is None or gal_lookup is None or by_n is None:
        gal_size, poly_lookup, gal_lookup, by_n = make_dictionaries(p, n, Gbound)
    for v in Partitions(n):
        for labels in itertools.product(*[itertools.combinations_with_replacement(by_n[m], e) for m, e in Counter(v).items()]):
            labels = Counter(flatten(labels))
            if Gbound is not None:
                # TODO: We could get a better lower bound by using subfields
                Glower = LCM([gal_size[gal_lookup[label]] for label in labels])
                if Glower > Gbound(n):
                    continue
            yield (labels, prod(prod(poly_lookup[label](x + i) for i in range(e)) for (label, e) in labels.items()), [gal_lookup[label] for label in labels])

def make_etale_nbound(p, nbound, Gbound=None):
    # TODO: think about Gbound; decreasing?, calling with n or nbound
    gal_size, poly_lookup, gal_lookup, by_n = make_dictionaries(p, nbound, Gbound)
    for n in range(1, nbound+1):
        yield from make_etale(p, n, Gbound=Gbound, gal_size=gal_size, poly_lookup=poly_lookup, gal_lookup=gal_lookup, by_n=by_n)

def padic_deg(label):
    pieces = label.split(".")
    return int(pieces[1]) * int(pieces[2])

def save_etale(labels, poly, gals, todofile, polyfolder, galfolder):
    is_field = len(labels) == 1 and list(labels.values()) == [1]
    labele = [label if e == 1 else f"{label}^{e}" for (label, e) in labels.items()]
    et_label = "*".join(labele)
    # Want better labels, but this is okay for now
    if is_field:
        with open(opj(galfolder, et_label), "w") as F:
            _ = F.write(gals[0])
    else:
        with open(todofile, "a") as Tout:
            _ = Tout.write(et_label + "\n")
        with open(opj(polyfolder,et_label), "w") as F: # TODO: use opj
            _ = F.write(f"{poly}")

# %attach etale_generation.py
# save_etale_nbound(2, 6, "gal_todo.txt", "etale_polys", "etale_gals")
def save_etale_nbound(ps, nbound, todofile, polyfolder, galfolder, Gbound=None):
    for p in ps:
        for labels, poly, gals in make_etale_nbound(p, nbound, Gbound=Gbound):
            save_etale(labels, poly, gals, todofile, polyfolder, galfolder)

def save_etale_n(ps, n, todofile, polyfolder, galfolder, Gbound=None):
    for p in ps:
        for labels, poly, gals in make_etale(p, n, Gbound=Gbound):
            save_etale(labels, poly, gals, todofile, polyfolder, galfolder)

args = parser.parse_args()
if args.prime_bound is not None:
    ps = prime_range(args.prime_bound + 1)
elif args.prime is not None:
    ps = ZZ(args.prime)
else:
    parser.error("Must specify either prime or prime_bound")

if os.path.exists(args.todofile):
    parser.error(f"Todo file {args.todofile} already exists")
os.makedirs(args.polyfolder, exist_ok=True)
if len(os.listdir(args.polyfolder)) > 0:
    parser.error(f"Folder {args.polyfolder} not empty")
os.makedirs(args.galfolder, exist_ok=True)
if len(os.listdir(args.galfolder)) > 0:
    parser.error(f"Folder {args.galfolder} not empty")
if args.degree_bound is not None:
    save_etale_nbound(ps, args.degree_bound, args.todofile, args.polyfolder, args.galfolder)
elif args.degree is not None:
    save_etale_n(ps, args.degree, args.todofile, args.polyfolder, args.galfolder)
else:
    parser.error("Must specify either degree or degree_bound")

sys.exit(0)
