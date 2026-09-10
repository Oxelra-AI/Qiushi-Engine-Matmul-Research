#!/usr/bin/env python3
"""Incompatibility graph from Wang LUT residual capacities for fixed matching strata.

For each fixed rank-1 matching M (including E11), each Wang occupation row
(subspace Phi, lower bound L) gives residual = (20 - L) - |M ∩ Phi\\{0}|.

  residual < 0  →  matching violates → stratum impossible
  residual = 0  →  vertex exclusion: all HR points in Phi forbidden
  residual = 1  →  edge exclusion: all HR pairs in Phi forbidden

Each exclusion carries the originating Wang row key for proof verification.
  A valid 20-point completion requires an independent set of size 20-|M|.
  For graph search results, exclusion is valid only when the independent-set
  search is exhaustive (or a separate upper-bound certificate is supplied). A
  small incumbent before timeout is only a lower bound on the independence
  number and must not close a stratum.
"""
import argparse, json, pathlib, pickle, sys, time

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import (
    unpack_basis, subspace_points_from_basis, matrix_rank_of_mask,
)

# ---- Optimized GF(2) membership ----

def make_pivot_dict(basis):
    """Build pivot dict for fast repeated in_rowspace queries."""
    return {b.bit_length() - 1: b for b in basis if b}

def in_span_piv(piv, v):
    """Test if v is in span using precomputed pivot dict."""
    x = v
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None: return False
        x ^= b
    return True

# ---- Graph construction ----

def process_stratum(lut, matching, hr_set, hr_list):
    k = len(matching)
    target = 20 - k
    lb_min = max(20 - k - 1, 0)

    vex = {}; eex = {}; impossible = []
    n_r0 = n_r1 = n_filt = 0

    for key, lb in lut.items():
        if lb < lb_min: continue
        cap = 20 - lb
        needed = cap - 1   # min matching-in-span for residual ≤ 1
        if needed > k: continue
        n_filt += 1

        basis = unpack_basis(key)
        piv = make_pivot_dict(basis)

        # Count matching points in span with early exit
        cnt = 0
        bail = False
        for mi, m in enumerate(matching):
            if in_span_piv(piv, m): cnt += 1
            if cnt + (k - mi - 1) < needed:
                bail = True; break
        if bail: continue

        res = cap - cnt
        if res < 0:
            impossible.append({'key': int(key), 'lb': lb, 'cap': cap, 'cnt': cnt})
            continue

        if res == 0:
            n_r0 += 1
            for e in subspace_points_from_basis(basis):
                if e in hr_set and e not in vex:
                    vex[e] = int(key)
        elif res == 1:
            n_r1 += 1
            hrs = [e for e in subspace_points_from_basis(basis)
                   if e in hr_set and e not in vex]
            for i in range(len(hrs)):
                for j in range(i+1, len(hrs)):
                    pair = (min(hrs[i], hrs[j]), max(hrs[i], hrs[j]))
                    if pair not in eex:
                        eex[pair] = int(key)

    surv = [h for h in hr_list if h not in vex]
    ss = frozenset(surv)
    surv_eex = {p: v for p, v in eex.items() if p[0] in ss and p[1] in ss}

    return {
        'target': target, 'vex': vex, 'surv_eex': surv_eex, 'surv': surv,
        'impossible': impossible, 'n_r0': n_r0, 'n_r1': n_r1, 'n_filt': n_filt,
    }

# ---- Max independent set ----

def max_is_exact(adj, n, target, tlim=30.0):
    best = []
    t0 = time.time()
    to = [False]
    def bt(cur, cand):
        if to[0]: return
        if time.time() - t0 > tlim: to[0] = True; return
        if len(cur) + len(cand) <= len(best): return
        if not cand:
            if len(cur) > len(best): best[:] = list(cur)
            return
        v = max(cand, key=lambda x: len(adj[x] & cand))
        cur.append(v)
        bt(cur, cand - adj[v] - {v})
        cur.pop()
        if to[0] or (target and len(best) >= target): return
        bt(cur, cand - {v})
    bt([], set(range(n)))
    return len(best), sorted(best), not to[0]

# ---- Main ----

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--strata', required=True)
    ap.add_argument('--lut', default='data/'
                    'wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--k-filter', type=int, default=0)
    ap.add_argument('--out', required=True)
    ap.add_argument('--max-is-n', type=int, default=80)
    ap.add_argument('--is-time', type=float, default=30.0)
    args = ap.parse_args()

    # Rank-1 and HR point sets
    r1 = set()
    for u in range(1, 8):
        for v in range(1, 8):
            m = 0
            for i in range(3):
                if (u >> i) & 1: m |= v << (3*i)
            r1.add(m)
    hr_list = sorted(m for m in range(1, 512) if m not in r1)
    hr_set = frozenset(hr_list)
    assert len(hr_list) == 462

    # Load strata
    with open(args.strata) as f:
        sd = json.load(f)
    all_strata = []
    for k_str in sorted(sd['representatives_by_k'], key=int):
        for rep in sd['representatives_by_k'][k_str]:
            all_strata.append(rep)

    # Load LUT
    print(f"Loading LUT from {args.lut}...")
    t0 = time.time()
    with open(args.lut, 'rb') as f:
        data = pickle.load(f)
    lut = data['lut']
    print(f"  {len(lut):,} entries in {time.time()-t0:.1f}s")

    # lb histogram
    lb_hist = {}
    for lb_val in lut.values():
        lb_hist[lb_val] = lb_hist.get(lb_val, 0) + 1
    print(f"  lb range: {min(lb_hist)}..{max(lb_hist)}")

    results = []
    for idx, st in enumerate(all_strata):
        sk = st['k']
        if args.k_filter and sk != args.k_filter: continue
        matching = st['canonical']
        orb = st.get('orbit_image_count', '?')
        print(f"\n[{idx}] k={sk} orbit={orb} matching={matching}")

        ts = time.time()
        info = process_stratum(lut, matching, hr_set, hr_list)
        te = time.time() - ts

        rec = {
            'idx': idx, 'k': sk, 'matching': matching, 'orbit_size': orb,
            'target': info['target'],
            'impossible_rows': len(info['impossible']),
            'vertex_excluded': len(info['vex']),
            'surviving': len(info['surv']),
            'surviving_edges': len(info['surv_eex']),
            'res0_rows': info['n_r0'], 'res1_rows': info['n_r1'],
            'entries_tested': info['n_filt'],
            'elapsed_sec': round(te, 2),
        }

        if info['impossible']:
            rec['proof'] = 'matching_violates'
            rec['violating_row'] = info['impossible'][0]
        elif len(info['surv']) < info['target']:
            rec['proof'] = 'vertex_exclusion'
        elif len(info['surv']) <= args.max_is_n:
            surv = info['surv']
            si = {h: i for i, h in enumerate(surv)}
            n = len(surv)
            adj = [set() for _ in range(n)]
            for (h1, h2) in info['surv_eex']:
                adj[si[h1]].add(si[h2])
                adj[si[h2]].add(si[h1])
            degs = [len(a) for a in adj]
            rec['deg_min'] = min(degs) if degs else 0
            rec['deg_max'] = max(degs) if degs else 0
            rec['deg_mean'] = round(sum(degs)/n, 1) if n else 0
            rec['density'] = round(2*len(info['surv_eex'])/max(n*(n-1),1), 4)

            alpha, is_verts, opt = max_is_exact(adj, n, info['target'], args.is_time)
            rec['alpha'] = alpha
            rec['alpha_search_completed'] = opt
            rec['alpha_witness'] = [surv[i] for i in is_verts]
            if len(is_verts) >= info['target']:
                rec['proof'] = 'target_independent_set_found'
            elif opt and alpha < info['target']:
                rec['proof'] = 'exhaustive_vertex_plus_edge_exclusion'
            elif opt:
                rec['proof'] = 'exhaustive_but_target_not_excluded'
            else:
                rec['proof'] = 'unresolved_independent_set_search'
        else:
            rec['proof'] = 'graph_too_large'

        p = rec.get('proof', '?')
        print(f"  vex={rec['vertex_excluded']} surv={rec['surviving']} "
              f"se={rec['surviving_edges']} proof={p} ({te:.1f}s)")
        if 'alpha' in rec:
            print(f"  alpha={rec['alpha']} completed={rec['alpha_search_completed']}")

        results.append(rec)

    proved = sum(1 for r in results if r.get('proof') in
                 ('matching_violates', 'vertex_exclusion',
                  'exhaustive_vertex_plus_edge_exclusion'))
    out = {
        'total_tested': len(results), 'total_proved': proved,
        'lb_histogram': dict(sorted(lb_hist.items())),
        'results': results,
    }
    pathlib.Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, 'w') as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nSaved {args.out}")
    print(f"Proved: {proved}/{len(results)}")

if __name__ == '__main__':
    main()
