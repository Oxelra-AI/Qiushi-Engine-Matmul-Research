#!/usr/bin/env python3
"""Build PySAT sequential-counter CNF for rep10 dim1+through-4,6 and solve with CaDiCaL DRAT."""
import pickle, sys, time, hashlib, subprocess, json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from wang_capacity_lazy import unpack_basis, in_rowspace, subspace_points_from_basis, N
from pysat.card import CardEnc, EncType
from pysat.formula import CNF

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")

def sha256(p):
    h = hashlib.sha256()
    with open(p,'rb') as f:
        for c in iter(lambda: f.read(4*1024*1024), b''):
            h.update(c)
    return h.hexdigest()

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True)
    ap.add_argument("--timeout", type=int, default=7200)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    args.out.mkdir(parents=True, exist_ok=True)
    
    with open(LUT_PATH,'rb') as f:
        lut = pickle.load(f)['lut']
    
    fixed = [1, args.rep]
    fixed_set = set(fixed)
    dec_pts = sorted(p for p in range(1, 2**N) if p not in fixed_set)
    dp_set = set(dec_pts)
    n_dp = len(dec_pts)
    pt2var = {p: i+1 for i, p in enumerate(dec_pts)}
    
    formula = CNF()
    top = n_dp
    target = 20 - len(fixed)
    
    # Total support = target.  analysis correction: at-most and at-least
    # encoders must be created sequentially after updating `top`; otherwise
    # PySAT reuses the same auxiliary-variable interval for two different
    # sequential-counter circuits, making the equality inconsistent by itself.
    dp_lits = list(range(1, n_dp+1))
    card = CardEnc.atmost(dp_lits, target, top_id=top, encoding=EncType.seqcounter)
    top = max(top, card.nv)
    for cl in card.clauses:
        formula.append(cl)
    card = CardEnc.atleast(dp_lits, target, top_id=top, encoding=EncType.seqcounter)
    top = max(top, card.nv)
    for cl in card.clauses:
        formula.append(cl)
    
    n_wang = 0
    for key, lb in lut.items():
        basis = unpack_basis(key)
        dim = len(basis)
        cap = 20 - lb
        in_direct = (dim == 1)
        in_through = (dim in [4,6]) and all(in_rowspace(fp, basis) for fp in fixed)
        if not in_direct and not in_through:
            continue
        pts = subspace_points_from_basis(basis)
        fixed_in = sum(1 for fp in fixed if fp in set(pts))
        rcap = cap - fixed_in
        dp_in = [pt2var[p] for p in pts if p in dp_set]
        if not dp_in or rcap >= len(dp_in):
            continue
        if rcap <= 0:
            for v in dp_in:
                formula.append([-v])
        else:
            card = CardEnc.atmost(dp_in, rcap, top_id=top, encoding=EncType.seqcounter)
            top = max(top, card.nv)
            for cl in card.clauses:
                formula.append(cl)
        n_wang += 1
    
    build_time = time.time() - t0
    print(f"Formula: {top} vars, {len(formula.clauses)} clauses, {n_wang} Wang constraints")
    print(f"Build time: {build_time:.1f}s")
    
    cnf_path = args.out / "rep_seqcnt.cnf"
    formula.to_file(str(cnf_path))
    print(f"Saved: {cnf_path} ({cnf_path.stat().st_size / 1e6:.1f} MB)")
    
    # CaDiCaL with DRAT
    drat_path = args.out / "rep_seqcnt.drat"
    cad_log = args.out / "rep_seqcnt.cadical.log"
    
    print(f"Running CaDiCaL (timeout={args.timeout}s)...")
    t = time.time()
    try:
        proc = subprocess.run(
            ["cadical", "--unsat", "--binary=false", "-n", str(cnf_path), str(drat_path)],
            capture_output=True, text=True, timeout=args.timeout
        )
        cad_log.write_text(proc.stdout[-50000:] if len(proc.stdout) > 50000 else proc.stdout)
        cad_exit = proc.returncode
    except subprocess.TimeoutExpired:
        cad_exit = -1
        print("CaDiCaL timed out")
    
    cad_time = time.time() - t
    status = "UNSAT" if cad_exit == 20 else ("SAT" if cad_exit == 10 else f"EXIT_{cad_exit}")
    print(f"CaDiCaL: {status} in {cad_time:.1f}s")
    
    # DRAT verification
    verified = False
    trim_log = args.out / "rep_seqcnt.drat_trim.log"
    if cad_exit == 20 and drat_path.exists():
        print("Running drat-trim...")
        try:
            trim = subprocess.run(
                ["drat-trim", str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=1800
            )
            trim_log.write_text(trim.stdout[-50000:] if len(trim.stdout) > 50000 else trim.stdout)
            verified = "s VERIFIED" in (trim.stdout + trim.stderr)
            print(f"drat-trim: {'VERIFIED' if verified else 'NOT verified'}")
        except subprocess.TimeoutExpired:
            print("drat-trim timed out")
    
    meta = {
        "status": status, "drat_verified": verified,
        "vars": top, "clauses": len(formula.clauses), "wang_constraints": n_wang,
        "build_sec": build_time, "cadical_sec": cad_time,
        "total_sec": time.time() - t0,
        "fixed_points": fixed, "rank_s": 20,
        "hashes": {p.name: sha256(p) for p in [cnf_path, drat_path, trim_log]
                   if p.exists() and p.stat().st_size > 0},
    }
    (args.out / "meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True))
    print(json.dumps(meta, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
