#!/usr/bin/env python3
"""analysis: Lift-bit feasibility solver for quotient supports.

For a quotient support P under pivot q, each full-tensor Wang row W with q not in W
constrains the lift bits eps_p: the number of points whose chosen lift falls in W
must be at most cap20(W).

For p in P ∩ π(W), the chosen lift is in W iff eps_p = ell_W(p), where ell_W(p)=0
if lift0(p) in W, else ell_W(p)=1.

The constraint: #{p in P ∩ π(W) : eps_p = ell_W(p)} <= cap20(W).

In PB form: Σ_{p in agree0} (1-eps_p) + Σ_{p in agree1} eps_p <= cap20(W)
  where agree0 = P ∩ {p in π(W) : ell(p)=0}, agree1 = P ∩ {p in π(W) : ell(p)=1}.

Equivalently: |agree0| + Σ_{agree1} eps_p - Σ_{agree0} eps_p <= cap20(W)
  => Σ_{agree0} eps_p - Σ_{agree1} eps_p >= |agree0| - cap20(W)

For rows containing q: #{p in P ∩ π(W)} + 1 <= cap20(W), i.e. quotient occupation.
These involve no lift bits; if violated, support is infeasible regardless.

PARTIAL SUPPORT KEY PROPERTY: If the lift-bit system is UNSAT for partial support A,
then for any extension P ⊇ A, the system is also UNSAT (adding more points only adds
nonneg occupation). This gives reusable cut Σ_{p in A} x_p <= |A|-1.
"""
from __future__ import annotations
import json, struct, time, hashlib, sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

ROOT = Path('research/research_record')
WANG512_PATH = Path('data/wang_native/full_tensor/full_wang512_cap5_len20_all_dim3.bin')
OUTDIR = ROOT / 'workspace/data/quotient_lift'
OUTDIR.mkdir(parents=True, exist_ok=True)

PIVOTS = {'rank2': 17, 'rank3': 273}

def sha256(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def lift0(p, pivot):
    """Embed 8-bit quotient point p into 9-bit A-space, skipping pivot bit."""
    h = (pivot & -pivot).bit_length() - 1
    low = p & ((1 << h) - 1)
    high = (p >> h) << (h + 1)
    return low | high

def preprocess_wang512(pivot):
    """Preprocess WANG512 rows for a given pivot.
    
    Returns list of (cap20, contains_q, quotient_mask, agree0_mask, agree1_mask)
    where:
    - quotient_mask: bitmask of quotient points in π(W)
    - agree0_mask: quotient points p where lift0(p) ∈ W  (ell_W(p) = 0)
    - agree1_mask: quotient points p where lift1(p) ∈ W  (ell_W(p) = 1)
    """
    # Build lift maps
    lifts = []  # lifts[p] = (lift0, lift1) for quotient point p (1..255)
    for p in range(1, 256):
        a0 = lift0(p, pivot)
        a1 = a0 ^ pivot
        lifts.append((p, a0, a1))
    
    rows = []
    with open(WANG512_PATH, 'rb') as f:
        magic = f.read(8)
        assert magic == b'WANG512\x01', f"Bad magic: {magic}"
        n = struct.unpack('<I', f.read(4))[0]
        for idx in range(n):
            cap = struct.unpack('<B', f.read(1))[0]
            dim = struct.unpack('<B', f.read(1))[0]
            _res = struct.unpack('<H', f.read(2))[0]
            words = list(struct.unpack('<8Q', f.read(64)))
            
            def bit(words, p):
                return (words[p >> 6] >> (p & 63)) & 1
            
            cq = bool(bit(words, pivot))
            
            # Build quotient-space masks
            agree0 = 0  # points where lift0 ∈ W
            agree1 = 0  # points where lift1 ∈ W
            for p, a0, a1 in lifts:
                m0 = bool(bit(words, a0))
                m1 = bool(bit(words, a1))
                if m0:
                    agree0 |= 1 << (p - 1)  # 0-indexed bit for quotient point p
                if m1:
                    agree1 |= 1 << (p - 1)
            
            qmask = agree0 | agree1
            rows.append((cap, cq, qmask, agree0, agree1, dim))
    
    return rows

def solve_lift_bits_cpsat(support_mask, rows, pivot_name):
    """Given a quotient support as a bitmask, solve lift-bit feasibility.
    
    Returns (feasible, info_dict).
    """
    from ortools.sat.python import cp_model
    
    # Extract support points (0-indexed bits)
    points = []
    m = support_mask
    while m:
        b = m & (-m)
        points.append(b.bit_length() - 1)
        m ^= b
    n = len(points)
    
    model = cp_model.CpModel()
    eps = [model.NewBoolVar(f'e{points[i]}') for i in range(n)]
    point_to_idx = {points[i]: i for i in range(n)}
    
    n_quotient_violated = 0
    n_trivial = 0
    n_active = 0
    n_active_tight = 0
    constraint_info = []
    
    for cap, cq, qmask, ag0, ag1, dim in rows:
        active = support_mask & qmask
        k = bin(active).count('1')
        if k == 0:
            continue
        
        if cq:
            # Row contains q: quotient occupation check
            # k + 1 <= cap, i.e. k <= cap - 1
            if k > cap - 1:
                # Immediately infeasible regardless of lift bits
                n_quotient_violated += 1
                return False, {
                    'feasible': False,
                    'reason': 'quotient_occupation_violated',
                    'violated_dim': dim,
                    'violated_cap': cap,
                    'violated_k': k,
                    'support_size': n,
                }
            continue
        
        # Row does not contain q: lift-bit constraint
        # agree0 points: contribute (1 - eps) to "in W" count
        # agree1 points: contribute eps to "in W" count
        a0 = active & ag0  # selected points where lift0 in W
        a1 = active & ag1  # selected points where lift1 in W
        
        k0 = bin(a0).count('1')
        k1 = bin(a1).count('1')
        
        # Constraint: #{agree with W} <= cap
        # = (k0 - Σ_{a0} eps) + Σ_{a1} eps <= cap
        # = k0 + Σ_{a1} eps - Σ_{a0} eps <= cap
        # => Σ_{a0} eps - Σ_{a1} eps >= k0 - cap
        
        threshold = k0 - cap
        
        if threshold <= -(k0 + k1):
            # Always satisfied (even if all a0 have eps=0, all a1 have eps=1)
            n_trivial += 1
            continue
        
        n_active += 1
        if threshold == k0:
            n_active_tight += 1
        
        # Build constraint
        pos_vars = []  # eps variables with +1 coefficient (a0 points)
        neg_vars = []  # eps variables with -1 coefficient (a1 points)
        
        tmp = a0
        while tmp:
            b = tmp & (-tmp)
            idx = point_to_idx[b.bit_length() - 1]
            pos_vars.append(eps[idx])
            tmp ^= b
        
        tmp = a1
        while tmp:
            b = tmp & (-tmp)
            idx = point_to_idx[b.bit_length() - 1]
            neg_vars.append(eps[idx])
            tmp ^= b
        
        # Σ pos_vars - Σ neg_vars >= threshold
        model.Add(sum(pos_vars) - sum(neg_vars) >= threshold)
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60
    status = solver.Solve(model)
    
    feasible = status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    
    info = {
        'feasible': feasible,
        'status': solver.StatusName(status),
        'support_size': n,
        'n_quotient_violated': n_quotient_violated,
        'n_trivial': n_trivial,
        'n_active_constraints': n_active,
        'n_active_tight': n_active_tight,
    }
    
    if feasible:
        info['solution'] = {points[i]: solver.Value(eps[i]) for i in range(n)}
    
    return feasible, info


def solve_lift_bits_with_unsat_core(support_mask, rows, pivot_name, max_core_time=30):
    """Solve lift-bit feasibility and extract UNSAT core if infeasible.
    
    Returns (feasible, info_dict).
    If infeasible, info contains 'unsat_core_support_mask': minimal subset of
    support points that is already infeasible.
    """
    feasible, info = solve_lift_bits_cpsat(support_mask, rows, pivot_name)
    
    if feasible or info.get('reason') == 'quotient_occupation_violated':
        return feasible, info
    
    # Try to minimize the UNSAT core by removing points one at a time
    points = []
    m = support_mask
    while m:
        b = m & (-m)
        points.append(b.bit_length() - 1)
        m ^= b
    
    core_mask = support_mask
    for p in points:
        test_mask = core_mask & ~(1 << p)
        if test_mask == 0:
            continue
        f2, _ = solve_lift_bits_cpsat(test_mask, rows, pivot_name)
        if not f2:
            core_mask = test_mask  # Still infeasible without p
    
    info['unsat_core_support_mask'] = core_mask
    info['unsat_core_size'] = bin(core_mask).count('1')
    info['unsat_core_points'] = sorted([b for b in range(255) if (core_mask >> b) & 1])
    
    return False, info


def analyze_row_structure(support_mask, rows, pivot_name):
    """Analyze the constraint structure for a support, grouping by quotient subspace."""
    subspace_groups = defaultdict(list)
    
    for idx, (cap, cq, qmask, ag0, ag1, dim) in enumerate(rows):
        if cq:
            continue
        active = support_mask & qmask
        k = bin(active).count('1')
        if k == 0:
            continue
        
        # Group by (active quotient points, dimension)
        key = active
        subspace_groups[key].append({
            'row_idx': idx,
            'cap': cap,
            'dim': dim,
            'k': k,
            'agree0': active & ag0,
            'agree1': active & ag1,
        })
    
    # Summarize
    summary = {
        'num_subspace_groups': len(subspace_groups),
        'group_sizes': Counter(len(v) for v in subspace_groups.values()),
        'interesting_groups': [],
    }
    
    # Find groups where multiple rows constrain the same active points differently
    for active_mask, group in sorted(subspace_groups.items(), key=lambda kv: -len(kv[1])):
        k = bin(active_mask).count('1')
        patterns = set()
        min_cap = min(r['cap'] for r in group)
        for r in group:
            patterns.add((r['agree0'], r['agree1']))
        
        if len(patterns) > 1 or (k > min_cap):
            summary['interesting_groups'].append({
                'active_points': sorted([b for b in range(255) if (active_mask >> b) & 1]),
                'k': k,
                'num_rows': len(group),
                'num_distinct_patterns': len(patterns),
                'min_cap': min_cap,
                'slack': min_cap - k,  # negative = tight/violated even without lift info
            })
    
    summary['interesting_groups'].sort(key=lambda g: (g['slack'], -g['num_distinct_patterns']))
    summary['interesting_groups'] = summary['interesting_groups'][:30]
    
    return summary


def test_relaxation_supports():
    """Test lift-bit solver on the analysis relaxation supports from E11."""
    # These are E11 quotient supports, not rank-2/rank-3. But we can test the mechanism
    # on artificially constructed supports for rank-2 and rank-3.
    
    # First, let's test with small random supports to understand constraint density
    import random
    random.seed(42)
    
    results = {}
    for pname, pivot in PIVOTS.items():
        print(f"\nPreprocessing WANG512 for {pname} (pivot={pivot})...")
        t0 = time.time()
        rows = preprocess_wang512(pivot)
        prep_time = time.time() - t0
        print(f"  {len(rows)} rows preprocessed in {prep_time:.1f}s")
        
        # Count row types
        cq_count = sum(1 for r in rows if r[1])
        ncq_count = sum(1 for r in rows if not r[1])
        print(f"  Contains q: {cq_count}, not contains q: {ncq_count}")
        
        # Test with random 19-point supports
        tests = []
        for trial in range(5):
            pts = random.sample(range(255), 19)  # 0-indexed quotient bits
            mask = 0
            for p in pts:
                mask |= 1 << p
            
            t1 = time.time()
            feas, info = solve_lift_bits_cpsat(mask, rows, pname)
            solve_time = time.time() - t1
            info['trial'] = trial
            info['solve_time'] = solve_time
            info['support_points'] = sorted(pts)
            tests.append(info)
            print(f"  Trial {trial}: feasible={feas}, active={info.get('n_active_constraints','?')}, "
                  f"tight={info.get('n_active_tight','?')}, time={solve_time:.2f}s, reason={info.get('reason','')}")
        
        # Test with small supports (partial support pruning test)
        small_tests = []
        for trial in range(5):
            size = random.randint(3, 8)
            pts = random.sample(range(255), size)
            mask = 0
            for p in pts:
                mask |= 1 << p
            
            t1 = time.time()
            feas, info = solve_lift_bits_cpsat(mask, rows, pname)
            solve_time = time.time() - t1
            info['trial'] = trial
            info['solve_time'] = solve_time
            info['support_size_actual'] = size
            small_tests.append(info)
            print(f"  Small trial {trial} (size={size}): feasible={feas}, "
                  f"active={info.get('n_active_constraints','?')}, time={solve_time:.2f}s")
        
        # Analyze structure of one infeasible support (if any) or the tightest feasible one
        infeasible_examples = [t for t in tests if not t['feasible']]
        if infeasible_examples:
            print(f"  Found {len(infeasible_examples)} infeasible random 19-point supports!")
            # Try to find UNSAT core
            ex = infeasible_examples[0]
            mask = 0
            for p in ex['support_points']:
                mask |= 1 << p
            print(f"  Extracting UNSAT core for trial {ex['trial']}...")
            t1 = time.time()
            _, core_info = solve_lift_bits_with_unsat_core(mask, rows, pname)
            core_time = time.time() - t1
            print(f"  Core size: {core_info.get('unsat_core_size', 'N/A')}, time={core_time:.2f}s")
            tests[ex['trial']]['unsat_core'] = core_info
        
        results[pname] = {
            'pivot': pivot,
            'prep_time': prep_time,
            'total_rows': len(rows),
            'contains_q_rows': cq_count,
            'not_contains_q_rows': ncq_count,
            'full_support_tests': tests,
            'small_support_tests': small_tests,
        }
    
    return results


def main():
    t0 = time.time()
    results = test_relaxation_supports()
    results['elapsed_sec'] = time.time() - t0
    results['schema'] = 's0908_lift_bit_solver_v1'
    results['wang512_sha256'] = sha256(WANG512_PATH)
    
    out_path = OUTDIR / 'lift_bit_solver_test.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}")
    print(f"Total time: {results['elapsed_sec']:.1f}s")


if __name__ == '__main__':
    main()
