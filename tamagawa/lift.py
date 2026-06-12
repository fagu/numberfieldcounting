import pathlib
import re
import ast
import subprocess
import shutil
import time
import sys
from sage.all import ZZ, prod
from sage.libs.gap.libgap import libgap
from sage.databases.cremona import class_to_int
from collections import defaultdict


data = pathlib.Path("DATA")

def sort_key(label):
    """
    Sort labels first by the order of the group, then the tiebreaker, which may be an integer, a lower case Cremona code, or an underscore then upper case Cremona code (to support MacOS's case insensitivity).
    """
    N, i = label.split(".")
    N = int(N)
    if i[0] == "_":
        return [N, 1, class_to_int(i[1:].lower())]
    if i.isdigit():
        return [N, 0, int(i)]
    return [N, 0, class_to_int(i)]

def check_var(v):
    """
    Check that a user provided variable name is a valid GAP identifier.
    """
    return re.fullmatch("[a-zA-Z][a-zA-Z0-9_]*", v)

def check_vars(x):
    """
    Check that all user provided variable names are valid GAP identifiers and return them.

    INPUT:

    - ``x`` -- a comma separated string of variable names.
    """
    variables = [v.strip() for v in x.split(",")]
    invalid = [v for v in variables if not check_var(v)]
    if invalid:
        if len(invalid) == 1:
            msg = f"{invalid[0]} is not a valid variable name"
        else:
            msg = f"{','.join(invalid)} are not valid variable names"
        raise ValueError(msg)
    return variables

def check_valid_expr(x):
    """
    Check that an expression is valid defining a group element.

    INPUT:

    - ``x`` -- an ast Expression consisting of constants, names, negation, multiplication and exponentiation (parsed by Python as BitXor.  Note that BitXor has different precedence than exponentiation, so the parsed object from ast will not be correct, but it will be valid if and only if the expression will parse correctly as a group element in GAP.

    OUTPUT:

    Raises an error if the expression is not of the correct form, otherwise returns the set of all used variable names.
    """
    if isinstance(x, ast.BinOp):
        if x.op.__class__ not in [ast.BitXor, ast.Mult]:
            raise ValueError("Only multiplication and exponentiation allowed in relation")
        return check_valid_expr(x.left).union(check_valid_expr(x.right))
    elif isinstance(x, ast.UnaryOp):
        if x.op.__class__ != ast.USub:
            raise ValueError("Only multiplication, exponentiation and negation allowed in relation")
        return check_valid_expr(x.operand)
    elif isinstance(x, ast.Name):
        return {x.id}
    elif isinstance(x, ast.Constant):
        return set()
    else:
        raise ValueError(f"Only constants, variables, multiplication and exponentiation allowed; got {x.__class__.__name__}")

def check_valid_relation(x, variables, allow_mult=False):
    """
    Check that the given expression is a valid group element in the context that a given set of variables has been defined already.

    INPUT:

    - ``x`` -- a string, expressing a group element in terms of the specified variables and the normal group operations.
    - ``variables`` -- a set of already-defined variable names
    - ``allow_mult`` -- whether to allow multiple lines in ``x``

    OUTPUT:

    Raises an error if x does not parse or if there are undefined variables; returns the lines in x as a list of strings otherwise.
    """
    try:
        parsed = ast.parse(x).body
    except Exception as err:
        raise ValueError(f"Relation does not parse: {str(err)}")
    if not allow_mult and len(parsed) > 1:
        raise ValueError("Relation must be a single expression")
    for r in parsed:
        undefined = check_valid_expr(r.value).difference(variables)
        if undefined:
            raise ValueError(f"Undefined variables: {','.join(undefined)}")
    return [line for line in x.split("\n") if line.strip()]

def check_valid_defs(x, variables):
    """
    Check that the given definition sequence is valid, and return it in a normalized form for inclusion in a GAP function.

    INPUT:

    - ``x`` -- a string, with each line defining a variable in terms of previous variables.
    - ``variables`` -- a set of initially defined variable names.

    OUTPUT:

    A normalized string, appropriate for inclusion in a GAP function.
    """
    lines = x.split("\n")
    for i, line in enumerate(lines):
        if line.count("=") != 1:
            raise ValueError("Each line in the definition section must set the value of one variable")
        pieces = line.split("=")
        v = pieces[0].rstrip(":").strip()
        if not check_var(v):
            raise ValueError(f"{v} is not a valid variable name")
        rhs = pieces[1].rstrip(";").strip()
        check_valid_relation(rhs, variables)
        variables.add(v)
        lines[i] = f"{v} := {rhs};"
    return "\n    ".join(lines), variables

def setup_gap_script(p, Fpath=None):
    """
    Converts the relation file into a GAP script defining CheckRel and LiftGal methods.
    """
    if Fpath is None:
        Fpath = data / str(p) / "rel.txt"
    with open(Fpath) as F:
        pieces = F.read().split("\n\n")
        if len(pieces) == 2:
            variables = check_vars(pieces[0])
            defs, allvars = "", set(variables)
            rels = check_valid_relation(pieces[1], allvars, allow_mult=True)
        elif len(pieces) == 3:
            variables = check_vars(pieces[0])
            defs, allvars = check_valid_defs(pieces[1], set(variables))
            rels = check_valid_relation(pieces[2], allvars, allow_mult=True)
        else:
            raise ValueError(f"Relation file {Fpath} must have either two or three sections")
    script_path = data / str(p) / "lift.g"
    with open(script_path, "w") as Fout:
        varset = "\n    ".join(f"{v} := tup[{i}];" for i,v in enumerate(variables,1))
        rels = " and ".join(f"{rel} = tup[1]^0" for rel in rels)
        _ = Fout.write(f"""CheckRel := function(tup)
    local {', '.join(sorted(allvars))};
    {varset}
    {defs}
    return {rels};
end;

""")
        with open("lift.g") as F:
            _ = Fout.write(F.read())

def make_eltstore(p, recursing):
    """
    Creates a cache folder that stores in progress computations.  Checks that the relation file hasn't changed,
    deleting the cache if it has.
    """
    datap = data / str(p)
    eltstore = datap / "eltstore"
    toppath = pathlib.Path("rel.txt")
    relpath = datap / "rel.txt"
    if toppath.exists():
        shutil.copy(toppath, relpath)
    if not relpath.exists():
        raise ValueError("No relation given in rel.txt")
    with open(relpath) as F:
        contents = F.read()
        pieces = contents.split("\n\n")
        r = pieces[0].count(",") - 1
        if r <= 0:
            raise ValueError("Must provide at least one wild generator")
        if recursing:
            # We've already dealt with clearing eltstore in the parent process
            return r, eltstore
        newhash = hash(contents)
        relhash = datap / "relhash"
        if relhash.exists():
            with open(relhash) as F:
                curhash = int(F.read())
        else:
            curhash = None
        if eltstore.exists() and curhash is not None and newhash != curhash:
            shutil.rmtree(eltstore)
    with open(relhash, "w") as F:
        _ = F.write(str(newhash))
    setup_gap_script(p)
    eltstore.mkdir(exist_ok=True)
    (datap / "race").mkdir(exist_ok=True)
    return r, eltstore

def case_label(label):
    # Ugh; MacOS is case insensitive
    N, i = label.split(".")
    if i[0] != "_" and i.isupper():
        return f"{N}._{i}"
    return label

def actual_counts(p):
    """
    Reads the computed counts (from a specified presentation) into a dictionary
    """
    eltstore = data / str(p) / "eltstore"
    cnt = {}
    for path in eltstore.iterdir():
        with open(path) as F:
            c = 0
            for line in F:
                if line.strip():
                    c += 1
            cnt[path.name] = c
    return cnt

def is_saved(label, datap):
    """
    Checks if tuples have been saved for the given label.

    INPUT:

    - ``label`` -- the label of a group from gps.txt
    - ``datap`` -- a Path object for ``data/p/``
    """
    return (datap / "eltstore" / label).exists()

def load_elts(label, datap, gps):
    """
    Loads saved tuples into a list of GAP elements suitable for further lifting.

    INPUT:

    - ``label`` -- the label of a group from gps.txt
    - ``datap`` -- a Path object for ``data/p/``
    - ``gps`` -- the dictionary produced by load_groups
    """
    with open(datap / "eltstore" / label) as F:
        T = gps[label]
        return [[libgap.LoadElt(ZZ(x), T) for x in line.strip().split(",")] for line in F if line.strip()]

def save_elts(elts, label, datap, gps):
    """
    INPUT:

    - ``elts`` -- a list of lists of GAP elements, storing the lifted tuples for a given group.
    - ``label`` -- the label of the group containing the elements
    - ``datap`` -- a Path object for ``data/p``
    - ``gps`` -- the dictionary produced by load_groups
    """
    race = (datap / "race" / label)
    race.touch()
    with open(datap / "eltstore" / label, "w") as F:
        T = gps[label]
        _ = F.write("\n".join(",".join(str(libgap.SaveElt(g, T)) for g in tup) for tup in elts) + "\n")
    race.unlink()

def clear_race(p):
    """
    If a verification run was interrupted in the middle of writing to disk,
    it's possible that eltstore could be corrupted.  To prevent this, a race folder exists.
    This function is called to clean up any files that were not completed correctly.
    """
    datap = data / str(p)
    eltstore = datap / "eltstore"
    for race in list((datap / "race").iterdir()):
        label = race.name
        race.unlink()
        (eltstore / label).unlink(missing_ok=True)

def vprint(s, verbose):
    """
    A utilty function that prints the string ``s`` only if ``verbose`` is true.
    """
    if verbose:
        print(s)

def set_abort(p):
    """
    Creates a file signaling that an early abort has been triggered (allowing other processes to abort).

    Also raises an error so this process stops.
    """
    fname = data / str(p) / "abort"
    fname.touch()
    raise ValueError("Aborting (mismatched count)")

def check_abort(p):
    """
    Checks whether another process has created an early abort file, raising a KeyboardInterrupt if so.
    """
    fname = data / str(p) / "abort"
    if fname.exists():
        print("Early abort: mismatched count")
        raise KeyboardInterrupt

def clear_abort(p):
    """
    Delete any created early abort file, in preparation for future runs.
    """
    fname = data / str(p) / "abort"
    fname.unlink(missing_ok=True)

def status(p, gps, cache, slen):
    """
    Prints a status report, based on progress from subprocesses.

    INPUT:

    - ``p`` -- the prime being run
    - ``gps`` -- the dictionary produced by load_groups
    - ``cache`` -- a dictionary for saving counts computed by counting lines in the ``eltstore`` folder.
      This dictionary is progressively updated upon each call to this function.
    - ``slen`` -- the length of the previous status message

    OUTPUT:

    The length of this status message.
    """
    if not gps:
        return
    eltstore = data / str(p) / "eltstore"
    gnum = 0 # number of finished groups
    gden = len(gps)
    enum = 0 # number of finished elements
    eden = 0
    for label in gps:
        N = int(label.split(".")[0])
        eden += N
        path = eltstore / label
        if path.exists():
            gnum += 1
            enum += N
    msg = f"{gnum}/{gden} groups done ({gnum/gden:.2%}, {enum/eden:.2%} by size)"
    if len(msg) < slen:
        msg, slen = msg + " "*(slen - len(msg)), len(msg)
    else:
        slen = len(msg)
    print(msg, end="\r")
    return slen

def report(p, gps, projelts=None, interrupted=False):
    """
    Print a final report saying whether lifting was successful.

    INPUT:

    - ``p`` -- the prime being run
    - ``gps`` -- the dictionary produced by ``load_groups``
    - ``projelts`` -- the dictionary containing tuples constructed in ``main``.  If not provided, counts are read using ``actual_counts``.
    - ``interrupted`` -- whether this report is being issued after the main process received a KeyboardInterrupt
    """
    clear_abort(p)
    clear_race(p)
    if projelts is None:
        actual = actual_counts(p)
    else:
        actual = {label: len(L) for label,L in projelts.items()}
    bad = []
    missing = []
    for label in gps:
        if label not in actual:
            missing.append(label)
    if not missing and not interrupted:
        print("Lifting successful!")
    else:
        if interrupted:
            print("Interrupted, quitting...")
        elif missing:
            print("Verification not completely successful")
        if missing and not interrupted:
            missing.sort(key=sort_key)
            if len(missing) == 1:
                print(f"The verification script did not finish for {missing[0]}")
            elif len(missing) < 10:
                print(f"For the following {len(missing)} groups, the verification script did not finish: {', '.join(missing)}")
            else:
                print(f"The verification script did not finish for {len(missing)} groups: {', '.join(missing[:4])}...")

def load_tree(datap, base, verbose):
    if base is None:
        tree = None
    else:
        vprint(f"Lifting from base {base}", verbose)
        tree = {base}
    projcod = {}
    with open(datap / "proj.txt") as F:
        for line in F:
            domain, codomain, ischar, imgs = line.strip().split("|")
            projcod[domain] = codomain
            if base is not None and codomain in tree:
                tree.add(domain)
    return projcod, tree

def load_groups(p, base, tree, qonly, qcutoff, verbose):
    vprint("Loading groups...", verbose)
    from sage.libs.gap.util import GAPError
    datap = data / str(p)
    gps = {}
    gens = {}
    with open(datap / "gps.txt") as F:
        for line in F:
            label, desc, elts = line.strip().split("|")
            if base is not None and label not in tree:
                continue
            if qonly or qcutoff is not None:
                N = ZZ(label.split(".")[0])
                pp, k = N.is_prime_power(get_data=True)
                if (qonly and pp != p and N != 1) or (qcutoff is not None and pp == p and k > qcutoff):
                    continue
            if elts:
                elts = elts.split(",")
            else:
                elts = []
            gps[label] = G = libgap.StringToGroup(desc)
            gens[label] = [libgap.LoadElt(ZZ(x), G) for x in elts]
    return gps, gens

def load_proj(datap, gps, gens, base, tree, verbose):
    vprint("Loading projections...", verbose)
    proj = defaultdict(list)
    with open(datap / "proj.txt") as F:
        for line in F:
            domain, codomain, ischar, imgs = line.strip().split("|")
            if domain not in gps or base is not None and codomain not in tree:
                # qcutoff was set, or we are not above the specified base
                continue
            dom = gps[domain]
            cod = gps[codomain]
            ischar = (ischar == "1")
            pi = libgap.GroupHomomorphismByImages(dom, cod, gens[domain], [libgap.LoadElt(ZZ(x), cod) for x in imgs.split(",")])
            proj[domain].append((codomain, ischar, pi))
    return proj

def initialize_projelts(datap, gps, base, tree, r, verbose):
    vprint(f"Loading saved tuples...", verbose)
    projelts = {}
    for label in tree:
        if is_saved(label, datap):
            projelts[label] = load_elts(label, datap, gps)
    tame = set()
    if base is None:
        vprint("Loading tame elts...", verbose)
        with open(datap / "tame.txt") as F:
            for line in F:
                label, elts = line.strip().split("|")
                if label not in gps:
                    # qcutoff was set
                    continue
                tame.add(label)
                if label in projelts:
                    # Already loaded from saved data
                    continue
                T = gps[label]
                elts = elts.split(";")
                elts = [[libgap.LoadElt(ZZ(x), T) for x in y.split(",")] + [T.One() for _ in range(r)] for y in elts]
                projelts[label] = elts
                save_elts(elts, label, datap, gps)
    return projelts, tame

def prep_parallel(datap, gps, base_limit, tame, projcod, projelts):
    if base_limit is None:
        base_limit = 100
    endpoint = {t:t for t in tame}
    for domain, codomain in projcod.items():
        if domain not in gps:
            # qcutoff or qonly was set
            continue
        N = int(domain.split(".")[0])
        if N <= base_limit:
            endpoint[domain] = domain
        else:
            endpoint[domain] = endpoint[codomain]
    by_endpoint = defaultdict(list)
    for domain, ep in endpoint.items():
        by_endpoint[ep].append(domain)
    tree = [ep for ep in by_endpoint if ep not in projelts]
    bases = [ep for ep,domains in by_endpoint.items() if any(domain not in projelts for domain in domains)]
    with open(datap / "bases.txt", "w") as F:
        _ = F.write("\n".join(bases) + "\n")
    return tree

def run_lifting(p, projelts, gps, proj, tree, verbose):
    datap = data / str(p)
    vprint("Lifting tuples...", verbose)
    slen = 0
    cache = {}
    for label in tree:
        G = gps[label]
        if label not in projelts:
            vprint(f"Starting {label}...", verbose)
            codomain, ischar, pi = proj[label][0]
            projelts[label] = elts = libgap.LiftGal(projelts[codomain], pi, ischar, 0)
            save_elts(elts, label, datap, gps)
            if not verbose:
                slen = status(p, gps, cache, slen)
    if not verbose:
        print(" "*slen)

def get_subprocess_cmd(p, ncores, timeout, qcutoff, verbose):
    datap = data / str(p)
    timeout = f" --timeout {timeout}" if timeout else ""
    k = f" -k {qcutoff}" if qcutoff is not None else ""
    v = " -v" if verbose else ""
    return "parallel -j %s%s -a %s ./verify -p %s%s%s -b {1}" % (ncores, timeout, datap / "bases.txt", p, k, v)

def run_subprocess(p, gps, ncores, qcutoff, timeout, verbose):
    cmd = get_subprocess_cmd(p, ncores, timeout, qcutoff, verbose)
    if verbose:
        subprocess.run(cmd, shell=True)
    else:
        print("Starting parallel subprocess")
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            cache = {}
            slen = 0
            while True:
                time.sleep(1) # TODO: Reset to 0.2
                code = proc.poll()
                if code is not None:
                    print(" "*slen) # Clear progress message
                    if code != 0:
                        print(f"parallel terminated with exit code {code}")
                    break
                if early_abort:
                    check_abort()
                slen = status(p, gps, cache, slen)
        except KeyboardInterrupt:
            print(" "*slen)
            proc.terminate() # Stops new jobs from being created
            proc.terminate() # Kills running jobs
            report(p, gps, interrupted=True)
            time.sleep(1)
            proc.kill()
            sys.exit(130)


def main(p, base=None, base_limit=None, qcutoff=None, qonly=False, ncores=None, timeout=None, verbose=False):
    """
    The main counting function: loads data from appropriate files, lifts tuples to find homs.

    INPUT:

    - ``base`` -- a group label.  If provided, only groups mapping to the specified base will be computed.  Mainly used by subprocesses in a parallelized computation.
    - ``base_limit`` -- an integer, the limit on the size of groups computed in an initial run before splitting into subprocesses.  Only used if ncores is also provided, defaults to 100.
    - ``qcutoff`` -- if provided, p-groups whose order is larger than p^qcutoff are omitted
    - ``qonly`` -- if true, only p-groups are counted
    - ``ncores`` -- the number of cores to use
    - ``verbose`` -- if true, more details about which groups are in progress will be shown.  Note that setting verbose to true will disable the ongoing status report if run in parallel.
    - ``timeout`` -- passed on to GNU parallel, setting a maximum time used for each subprocess.  May not work on MacOS.
    """
    print("Setting up computation...")
    datap = data / str(p)
    r, eltstore = make_eltstore(p, base is not None)
    libgap.InfoPerformance.SetInfoLevel(0) # Skip messages about "If you gave a domain and not seeds consider `OrbitsDomain' instead."
    libgap.Read("IO.g")
    libgap.Read(str(datap / "lift.g"))
    projcod, tree = load_tree(datap, base, verbose)

    gps, gens = load_groups(p, base, tree, qonly, qcutoff, verbose)

    proj = load_proj(datap, gps, gens, base, tree, verbose)
    if base is None:
        tree = list(gps)
    else:
        tree = [label for label in gps if label in tree]

    projelts, tame = initialize_projelts(datap, gps, base, tree, r, verbose)
    if base is None and ncores is not None:
        tree = prep_parallel(datap, gps, base_limit, tame, projcod, projelts)

    run_lifting(p, projelts, gps, proj, tree, verbose)

    if base is None:
        if ncores is not None:
            report(p, gps, projelts)
        else:
            run_subprocess(p, gps, ncores, qcutoff, timeout, verbose)
            report(p, gps)
