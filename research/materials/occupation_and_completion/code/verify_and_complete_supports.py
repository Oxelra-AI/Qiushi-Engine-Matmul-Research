#!/usr/bin/env python3
"""Verify orbit-branch DFS solutions against the FULL quotient Wang system,
then pipe survivors to fixed-A Brent completion.

If a support is Wang-admissible AND has a Brent completion, we have a
rank-19 quotient decomposition => rank-22 full algorithm!
"""
from __future__ import annotations

import json
import os
import struct
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from quotient_line_caps_and_controls import (
    quotient_tensor, quotient_project, vec, gf2_rank_mat, bits_to_mat,
    recon_quotient,
)

OUTDIR = SESSION / "workspace/data/constructive_pipeline"


def load_binary_constraints(path: str):
    """Load E11WANG1 format."""
    rows = []
    with open(path, 'rb') as f:
        magic = f.read(8)
        assert magic == b'E11WANG1'
        nrows = struct.unpack('<I', f.read(4))[0]
        for _ in range(nrows):
            hdr = f.read(4)
            cap = hdr[0]
            words = list(struct.unpack('<4Q', f.read(32)))
            rows.append((cap, words))
    return rows


def check_wang_admissible(support, constraints):
    """Check if support satisfies all Wang constraints. Return violation count."""
    violations = 0
    support_set = set(support)
    for cap, words in constraints:
        occ = 0
        for p in support_set:
            if words[p >> 6] & (1 << (p & 63)):
                occ += 1
        if occ > cap:
            violations += 1
    return violations


def fixed_a_brent_sat(support, pivot, rank, timeout=30):
    """Run fixed-A Brent completion for a quotient support via CaDiCaL."""
    from quotient_core_sat import Encoder
    
    # Create a known_terms list with only A-supports fixed, B/C unknown
    # Actually, the Encoder expects full terms for known_units mode.
    # We need a different approach: generate CNF with A-supports as unit clauses.
    
    cnf = Encoder(pivot, rank, sort_u=True, capacity=True)
    cnf.make_base()
    cnf.add_brent()
    cnf.add_capacity()
    cnf.add_sort()
    
    # Add unit clauses fixing the A-support
    support_sorted = sorted(support)
    for t, u_val in enumerate(support_sorted):
        for bit in range(8):
            var = cnf.u[t][bit]
            if (u_val >> bit) & 1:
                cnf.F.unit(var)
            else:
                cnf.F.unit(-var)
    
    cnf.F.comments.append(f'fixed_A_support={support_sorted}')
    
    # Write CNF
    cnf_path = OUTDIR / f"fixedA_p{pivot}_n{rank}_{hash(tuple(support_sorted)) & 0xFFFFFFFF:08x}.cnf"
    cnf.F.write(cnf_path)
    
    # Run CaDiCaL
    result = subprocess.run(
        ['cadical', '-t', str(timeout), str(cnf_path)],
        capture_output=True, text=True, timeout=timeout + 10
    )
    
    sat = 'SATISFIABLE' in result.stdout
    unsat = 'UNSATISFIABLE' in result.stdout
    
    return {
        'support': support_sorted,
        'cnf_path': str(cnf_path),
        'vars': cnf.F.nv,
        'clauses': len(cnf.F.clauses),
        'sat': sat,
        'unsat': unsat,
        'unknown': not sat and not unsat,
        'returncode': result.returncode,
    }


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3"], default="rank3")
    ap.add_argument("--pivot", type=int, default=0)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--solutions", type=str, nargs='+',
                    help="JSON arrays of supports to check")
    ap.add_argument("--max-check", type=int, default=20)
    ap.add_argument("--brent-timeout", type=int, default=30)
    args = ap.parse_args()
    
    OUTDIR.mkdir(parents=True, exist_ok=True)
    pivots = {"rank2": 17, "rank3": 273}
    pivot = args.pivot if args.pivot else pivots[args.pivot_name]
    
    # Load full constraint system
    bin_path = SESSION / f"workspace/data/wang_native/quotient_binaries/{args.pivot_name}_all_n{args.target}.bin"
    print(f"Loading full constraints from {bin_path}...")
    constraints = load_binary_constraints(str(bin_path))
    print(f"  Loaded {len(constraints)} rows")
    
    # Hardcoded solutions from the orbit-branch DFS
    # Rank-3 branch 5 solutions
    solutions_r3_b5 = [
        [94,95,96,97,98,100,101,103,104,105,107,108,109,110,111,112,113,116,117],
        [94,95,96,97,98,100,101,103,104,105,107,108,109,110,111,112,113,116,118],
    ]
    # Rank-3 branch 4 solutions
    solutions_r3_b4 = [
        [12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30],
        [12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,32],
    ]
    
    all_solutions = solutions_r3_b5 + solutions_r3_b4
    
    results = []
    for i, supp in enumerate(all_solutions[:args.max_check]):
        print(f"\n  Support {i}: {supp}")
        viols = check_wang_admissible(supp, constraints)
        print(f"    Wang violations (full system): {viols}")
        
        result = {'index': i, 'support': supp, 'wang_violations': viols}
        
        if viols == 0:
            print(f"    WANG-ADMISSIBLE! Running Brent completion...")
            brent = fixed_a_brent_sat(supp, pivot, args.target, args.brent_timeout)
            result['brent'] = brent
            if brent['sat']:
                print(f"    *** SAT! RANK-19 QUOTIENT DECOMPOSITION FOUND! ***")
            elif brent['unsat']:
                print(f"    UNSAT: no Brent completion exists for this support")
            else:
                print(f"    UNKNOWN: timeout ({args.brent_timeout}s)")
        else:
            print(f"    NOT Wang-admissible, skipping Brent completion")
        
        results.append(result)
    
    summary = {
        "pivot_name": args.pivot_name,
        "pivot": pivot,
        "target": args.target,
        "total_checked": len(results),
        "wang_admissible": sum(1 for r in results if r['wang_violations'] == 0),
        "brent_sat": sum(1 for r in results if r.get('brent', {}).get('sat', False)),
        "brent_unsat": sum(1 for r in results if r.get('brent', {}).get('unsat', False)),
        "brent_unknown": sum(1 for r in results if r.get('brent', {}).get('unknown', False)),
        "results": results,
    }
    
    out_path = OUTDIR / "orbit_branch_verify_and_complete.json"
    out_path.write_text(json.dumps(summary, indent=2))
    print(f"\nSaved {out_path}")
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))


if __name__ == "__main__":
    main()
