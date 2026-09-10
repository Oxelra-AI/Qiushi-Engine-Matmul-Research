#!/usr/bin/env python3
"""Build conflict graph from cap-1 Wang rows and compute alpha(G).

For each quotient at target n=19, every cap-1 row of dim >= 2 defines a clique:
at most 1 of its points can be in a 19-element support.  Two points connected by
such a clique edge are mutually exclusive.  If the maximum independent set size
alpha(G) < 19, then no 19-element Wang-admissible support exists for that quotient.

The graph is built on 255 vertices (quotient points 1..255).
Edges: {u,v} if u and v both appear in some cap-1 row.
The cap-1 point rows (dim=1, 1 point each) are just self-loops and don't add edges.

Uses:
  - cliquer (command line) for exact alpha
  - PySAT for CNF independent-set encoding with CaDiCaL + DRAT
  - networkx for backup/verification
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SESSION = Path(os.path.dirname(os.path.abspath(__file__))).parent.parent
MAGIC = b"E11WANG1"


def load_binary(path: str | Path) -> list[tuple[int, int, list[int]]]:
    """Load E11WANG1 binary. Returns [(cap, dim8, points_list), ...]."""
    d = open(path, "rb").read()
    assert d[:8] == MAGIC
    n = struct.unpack("<I", d[8:12])[0]
    REC = struct.calcsize("<BBHQQQQ")
    rows = []
    off = 12
    for _ in range(n):
        cap, dim8, pad, w0, w1, w2, w3 = struct.unpack_from("<BBHQQQQ", d, off)
        off += REC
        pts = []
        for word_idx, w in enumerate([w0, w1, w2, w3]):
            for b in range(64):
                if (w >> b) & 1:
                    pts.append(64 * word_idx + b)
        rows.append((cap, dim8, pts))
    return rows


def build_conflict_graph(rows: list[tuple[int, int, list[int]]]) -> tuple[set[tuple[int, int]], dict]:
    """Build edge set from cap-1 rows (dim >= 2)."""
    edges: set[tuple[int, int]] = set()
    cap1_dim_hist: dict[int, int] = collections.Counter()
    clique_sizes: list[int] = []
    for cap, dim8, pts in rows:
        if cap != 1:
            continue
        cap1_dim_hist[dim8] += 1
        if dim8 < 2:
            continue  # point rows don't create edges
        clique_sizes.append(len(pts))
        for i in range(len(pts)):
            for j in range(i + 1, len(pts)):
                u, v = pts[i], pts[j]
                if u > v:
                    u, v = v, u
                edges.add((u, v))
    info = {
        "cap1_dim_hist": dict(sorted(cap1_dim_hist.items())),
        "cap1_clique_count": sum(1 for c, d, _ in rows if c == 1 and d >= 2),
        "edge_count": len(edges),
        "max_possible_edges": 255 * 254 // 2,
        "density": len(edges) / (255 * 254 / 2),
        "clique_size_hist": dict(collections.Counter(clique_sizes)),
    }
    return edges, info


def vertex_degrees(edges: set[tuple[int, int]]) -> dict[int, int]:
    deg: dict[int, int] = collections.Counter()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return dict(sorted(deg.items()))


def greedy_coloring_bound(edges: set[tuple[int, int]], n: int = 255) -> int:
    """Greedy coloring gives upper bound on chromatic number, lower bound on clique cover.
    Returns number of colors used = upper bound on chi(G), hence alpha(G) <= n/omega(Gbar)."""
    adj = [set() for _ in range(n + 1)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    # Greedy coloring in degree order
    order = sorted(range(1, n + 1), key=lambda x: -len(adj[x]))
    color = [0] * (n + 1)
    num_colors = 0
    for v in order:
        used = {color[u] for u in adj[v] if color[u] > 0}
        c = 1
        while c in used:
            c += 1
        color[v] = c
        if c > num_colors:
            num_colors = c
    return num_colors


def write_dimacs(edges: set[tuple[int, int]], path: str | Path, n: int = 255) -> None:
    """Write DIMACS graph file for cliquer."""
    with open(path, "w") as f:
        f.write(f"p edge {n} {len(edges)}\n")
        for u, v in edges:
            f.write(f"e {u} {v}\n")


def write_complement_dimacs(edges: set[tuple[int, int]], path: str | Path, n: int = 255) -> None:
    """Write complement graph for max-clique = alpha(G)."""
    all_edges = set()
    for u in range(1, n + 1):
        for v in range(u + 1, n + 1):
            if (u, v) not in edges:
                all_edges.add((u, v))
    with open(path, "w") as f:
        f.write(f"p edge {n} {len(all_edges)}\n")
        for u, v in all_edges:
            f.write(f"e {u} {v}\n")


def write_mis_cnf(edges: set[tuple[int, int]], target: int, path: str | Path, n: int = 255) -> int:
    """Write CNF for: does the conflict graph have an independent set of size >= target?
    
    Variables: x_1 .. x_255 (point i is in the set iff x_i is true).
    Clauses:
      - For each edge (u,v): NOT x_u OR NOT x_v  (at most one)
      - Cardinality >= target via sequential counter (Sinz encoding)
    
    Returns number of clauses.
    """
    clauses = []
    # Edge exclusion clauses
    for u, v in edges:
        clauses.append([-u, -v])

    # Sequential counter for sum(x_i) >= target
    # Auxiliary vars: s_{i,j} for i=1..n, j=1..target
    # s_{i,j} = true iff at least j of x_1..x_i are true
    # Base var offset: n+1
    pts = list(range(1, n + 1))
    k = target
    # s[i][j] : aux var for "at least j of first i vars are true"
    def s(i: int, j: int) -> int:
        return n + (i - 1) * k + j  # 1-indexed

    max_var = n + n * k

    # s(1,1) <=> x_1:  s(1,1) => x_1, x_1 => s(1,1)
    # But for >= encoding we only need the implication chain
    # Actually, for cardinality >= k, the standard Sinz at-most-k encoding 
    # is for <= k. For >= k we can negate: sum(-x_i) <= n-k.
    # Let's use the complement: introduce y_i = NOT x_i, then sum(y_i) <= n-k.
    # Sinz sequential counter for at-most-(n-k):
    
    nk = n - k  # at most nk of the y_i = NOT x_i can be true
    # i.e. at most nk of x_i can be false
    
    if nk < 0:
        # Impossible
        clauses.append([])  # empty clause
        with open(path, "w") as f:
            f.write(f"p cnf {max_var} {len(clauses)}\n")
            for c in clauses:
                f.write(" ".join(str(l) for l in c) + " 0\n")
        return len(clauses)
    
    if nk == 0:
        # All must be true
        for i in pts:
            clauses.append([i])
        with open(path, "w") as f:
            f.write(f"p cnf {n} {len(clauses)}\n")
            for c in clauses:
                f.write(" ".join(str(l) for l in c) + " 0\n")
        return len(clauses)

    # Sinz at-most-nk encoding for y_i = -x_i
    # Register vars: r_{i,j} for i=1..n, j=1..nk
    def r(i: int, j: int) -> int:
        return n + (i - 1) * nk + j

    max_var = n + n * nk

    # y_1 => r_{1,1}: -y_1 v r_{1,1} => x_1 v r_{1,1}
    clauses.append([pts[0], r(1, 1)])
    # NOT r_{1,j} for j=2..nk
    for j in range(2, nk + 1):
        clauses.append([-r(1, j)])
    
    # For i=2..n:
    for i in range(2, n + 1):
        # y_i => r_{i,1}: x_i v r_{i,1}
        clauses.append([pts[i - 1], r(i, 1)])
        # r_{i-1,1} => r_{i,1}
        clauses.append([-r(i - 1, 1), r(i, 1)])
        for j in range(2, nk + 1):
            # y_i AND r_{i-1,j-1} => r_{i,j}
            # i.e. x_i v -r_{i-1,j-1} v r_{i,j}
            clauses.append([pts[i - 1], -r(i - 1, j - 1), r(i, j)])
            # r_{i-1,j} => r_{i,j}
            clauses.append([-r(i - 1, j), r(i, j)])
        # y_i AND r_{i-1,nk} => false
        # i.e. x_i v -r_{i-1,nk}
        clauses.append([pts[i - 1], -r(i - 1, nk)])

    with open(path, "w") as f:
        f.write(f"p cnf {max_var} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(l) for l in c) + " 0\n")
    return len(clauses)


def run_cliquer(dimacs_path: str | Path, n: int = 255) -> dict:
    """Run cliquer on complement graph to find max independent set."""
    try:
        t0 = time.time()
        result = subprocess.run(
            ["cliquer", str(dimacs_path), "-a"],  # -a: all max cliques
            capture_output=True, text=True, timeout=600,
        )
        elapsed = time.time() - t0
        return {
            "stdout": result.stdout[:5000],
            "stderr": result.stderr[:2000],
            "returncode": result.returncode,
            "elapsed_sec": elapsed,
        }
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "elapsed_sec": 600}
    except FileNotFoundError:
        return {"error": "cliquer not found"}


def run_cadical_mis(cnf_path: str | Path, proof_path: str | Path, timeout: int = 300) -> dict:
    """Run CaDiCaL on the MIS CNF with DRAT proof."""
    try:
        t0 = time.time()
        result = subprocess.run(
            ["cadical", str(cnf_path), str(proof_path)],
            capture_output=True, text=True, timeout=timeout,
        )
        elapsed = time.time() - t0
        sat = None
        if result.returncode == 10:
            sat = True
        elif result.returncode == 20:
            sat = False
        return {
            "satisfiable": sat,
            "returncode": result.returncode,
            "elapsed_sec": elapsed,
            "stdout_tail": result.stdout[-3000:],
            "stderr_tail": result.stderr[-1000:],
            "proof_path": str(proof_path) if not sat else None,
        }
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "elapsed_sec": timeout}


def run_drat_trim(cnf_path: str | Path, proof_path: str | Path, timeout: int = 600) -> dict:
    """Verify DRAT proof with drat-trim."""
    try:
        t0 = time.time()
        result = subprocess.run(
            ["drat-trim", str(cnf_path), str(proof_path)],
            capture_output=True, text=True, timeout=timeout,
        )
        elapsed = time.time() - t0
        verified = "s VERIFIED" in result.stdout
        return {
            "verified": verified,
            "returncode": result.returncode,
            "elapsed_sec": elapsed,
            "stdout_tail": result.stdout[-2000:],
        }
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "elapsed_sec": timeout}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True, help="rank2 or rank3")
    ap.add_argument("--binary", required=True, help="path to E11WANG1 all-rows binary")
    ap.add_argument("--outdir", default=None)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--skip-cliquer", action="store_true")
    ap.add_argument("--skip-sat", action="store_true")
    ap.add_argument("--skip-drat", action="store_true")
    args = ap.parse_args()

    outdir = Path(args.outdir) if args.outdir else SESSION / "workspace/data/conflict_graph"
    outdir.mkdir(parents=True, exist_ok=True)

    print(f"Loading {args.binary}...")
    rows = load_binary(args.binary)
    print(f"  {len(rows)} rows loaded")

    print("Building conflict graph from cap-1 rows...")
    edges, info = build_conflict_graph(rows)
    print(f"  {info['cap1_clique_count']} cap-1 cliques (dim>=2)")
    print(f"  {info['edge_count']} edges, density {info['density']:.4f}")

    degs = vertex_degrees(edges)
    deg_vals = list(degs.values())
    # Vertices with no edges (isolated)
    isolated = [v for v in range(1, 256) if v not in degs]
    info["isolated_vertices"] = len(isolated)
    info["min_degree"] = min(deg_vals) if deg_vals else 0
    info["max_degree"] = max(deg_vals) if deg_vals else 0
    info["avg_degree"] = sum(deg_vals) / len(deg_vals) if deg_vals else 0
    
    # Greedy coloring bound
    num_colors = greedy_coloring_bound(edges)
    info["greedy_coloring_colors"] = num_colors
    info["greedy_alpha_upper_bound"] = 255 // (num_colors if num_colors > 0 else 1)
    # Actually: alpha <= n - chromatic number... no.
    # alpha(G) * omega(G) >= n (Ramsey-like), but not directly from coloring.
    # The coloring gives chi(G) >= omega(G), and alpha(G)*chi(G) >= n.
    # So alpha(G) >= n/chi(G) = 255/num_colors (lower bound, not useful for upper bound).
    # For upper bound: alpha(Gbar)*chi(Gbar) >= n, and omega(G) = chi(Gbar) heuristically.
    # Actually, a coloring of G with k colors means every color class is independent,
    # so the largest color class has size >= ceil(n/k).
    # This gives alpha(G) >= ceil(n/k), a LOWER bound.
    
    # For an UPPER bound on alpha, we need a clique cover of the complement,
    # or equivalently an independent set cover of G.
    # Better: compute max clique of complement directly.
    
    print(f"  Greedy coloring: {num_colors} colors (alpha >= {255 // num_colors})")
    print(f"  Degree range: {info['min_degree']}-{info['max_degree']}, avg {info['avg_degree']:.1f}")
    print(f"  Isolated vertices: {info['isolated_vertices']}")

    # Write DIMACS files
    dimacs_path = outdir / f"{args.pivot_name}_conflict.dimacs"
    write_dimacs(edges, dimacs_path)
    print(f"  DIMACS graph: {dimacs_path}")

    comp_dimacs_path = outdir / f"{args.pivot_name}_complement.dimacs"
    write_complement_dimacs(edges, comp_dimacs_path)
    comp_edges = 255 * 254 // 2 - len(edges)
    print(f"  Complement DIMACS: {comp_dimacs_path} ({comp_edges} edges)")

    # Run cliquer on complement graph to find max clique = alpha(G)
    cliquer_result = None
    if not args.skip_cliquer:
        print("\nRunning cliquer on complement graph (max clique = alpha(G))...")
        cliquer_result = run_cliquer(comp_dimacs_path)
        print(f"  Result: {json.dumps({k: v for k, v in cliquer_result.items() if k != 'stdout'}, indent=2)}")
        if "stdout" in cliquer_result:
            print(f"  stdout (first 2000 chars):\n{cliquer_result['stdout'][:2000]}")

    # Write MIS CNF and run CaDiCaL
    cnf_path = outdir / f"{args.pivot_name}_mis{args.target}.cnf"
    proof_path = outdir / f"{args.pivot_name}_mis{args.target}.drat"

    print(f"\nWriting MIS CNF (target={args.target})...")
    nclauses = write_mis_cnf(edges, args.target, cnf_path)
    print(f"  CNF: {cnf_path} ({nclauses} clauses)")

    cadical_result = None
    drat_result = None
    if not args.skip_sat:
        print(f"\nRunning CaDiCaL on MIS CNF...")
        cadical_result = run_cadical_mis(cnf_path, proof_path, timeout=300)
        print(f"  CaDiCaL result: {json.dumps({k: v for k, v in cadical_result.items() if 'stdout' not in k and 'stderr' not in k})}")
        if cadical_result.get("stdout_tail"):
            # Extract key stats
            for line in cadical_result["stdout_tail"].split("\n"):
                if any(w in line for w in ["conflicts", "decisions", "propagations", "time"]):
                    print(f"    {line.strip()}")

        if cadical_result.get("satisfiable") is False and not args.skip_drat:
            print(f"\nVerifying DRAT proof with drat-trim...")
            drat_result = run_drat_trim(cnf_path, proof_path)
            print(f"  drat-trim result: {json.dumps(drat_result)}")

    # Save results
    result = {
        "pivot_name": args.pivot_name,
        "target": args.target,
        "binary": str(args.binary),
        "graph_info": info,
        "dimacs_path": str(dimacs_path),
        "complement_dimacs_path": str(comp_dimacs_path),
        "cnf_path": str(cnf_path),
        "cliquer_result": cliquer_result,
        "cadical_result": cadical_result,
        "drat_result": drat_result,
    }
    out_path = outdir / f"{args.pivot_name}_conflict_graph_result.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nSaved: {out_path}")


if __name__ == "__main__":
    main()
