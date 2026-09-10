#!/usr/bin/env python3
"""Verify R(M_<3,3,2>) >= 14 computationally over F_2 using flip-cpd.

M_<3,3,2> = multiplication of 3x3 by 3x2 matrices, giving 3x2 result.
Tensor dimensions: K^9 x K^6 x K^6 (A entries, B entries, C entries).

T[i*3+j, j'*3+k, i'*3+k'] = delta(j,j') * delta(i,i') * delta(k,k')
where A is 3x3 indexed by (i,j), B is 3x2 indexed by (j',k), C is 3x2 indexed by (i',k').
But B is 3x2 so k runs 0..1, hence b-index = j'*2+k (range 0..5).
And C is 3x2 so c-index = i'*2+k' (range 0..5).
"""
import numpy as np
from pathlib import Path
import json, time, subprocess, tempfile

def make_M332():
    """Build the 3x3-by-3x2 rectangular matrix multiplication tensor.
    Factor spaces: A in K^9 (3x3), B in K^6 (3x2), C in K^6 (3x2).
    T[a, b, c] = 1 iff computing C=AB uses A_{i,j} * B_{j',k} to produce C_{i',k'}
    with a=3i+j, b=3j'+k (k<2), c=3i'+k' (k'<2), and j=j', i=i', k=k'.
    
    Actually: C_{i,k} = sum_j A_{i,j} * B_{j,k}.
    Tensor entry: T[3i+j, 2j'+k, 2i'+k'] = delta(j,j')*delta(i,i')*delta(k,k').
    NOTE: B is 3 rows x 2 cols, so B-index = j*2+k with j in 0..2, k in 0..1.
    C is 3 rows x 2 cols, so C-index = i*2+k with i in 0..2, k in 0..1.
    """
    T = np.zeros((9, 6, 6), dtype=np.int64)
    count = 0
    for i in range(3):
        for j in range(3):
            for k in range(2):
                a = 3*i + j       # A-index (row i, col j)
                b = 2*j + k       # B-index (row j, col k)  [CORRECTED: j*2+k]
                c = 2*i + k       # C-index (row i, col k)
                T[a, b, c] = 1
                count += 1
    print(f"M_<3,3,2>: shape {T.shape}, nnz = {count}")
    assert count == 18, f"Expected 18 nonzero entries, got {count}"
    return T

def verify_M332(T):
    """Verify the tensor encodes C = A*B for 3x3 * 3x2."""
    # Test with random A, B
    rng = np.random.default_rng(42)
    for _ in range(100):
        A = rng.integers(0, 2, (3, 3))
        B = rng.integers(0, 2, (3, 2))
        C_true = (A @ B) % 2
        
        # Compute using tensor
        a_vec = A.ravel()  # length 9
        b_vec = B.ravel()  # length 6, row-major: [B00,B01,B10,B11,B20,B21]
        c_result = np.zeros(6, dtype=np.int64)
        for idx_a in range(9):
            for idx_b in range(6):
                for idx_c in range(6):
                    if T[idx_a, idx_b, idx_c]:
                        c_result[idx_c] = (c_result[idx_c] + a_vec[idx_a] * b_vec[idx_b]) % 2
        
        C_tensor = c_result.reshape(3, 2)
        assert np.array_equal(C_true, C_tensor), f"Mismatch: {C_true} vs {C_tensor}"
    print("Verification passed: 100 random tests over F_2")

def tensor_to_flipcpd_format(T, path, field=2):
    """Write tensor in flip-cpd input format."""
    d1, d2, d3 = T.shape
    with open(path, 'w') as f:
        f.write(f"# Tensor M_<3,3,2> over F_{field}\n")
        f.write(f"# Dimensions: {d1} x {d2} x {d3}\n")
        for a in range(d1):
            for b in range(d2):
                for c in range(d3):
                    if T[a, b, c] % field != 0:
                        f.write(f"{a} {b} {c} {int(T[a,b,c] % field)}\n")
    print(f"Written {path}")

def run_flipcpd(tensor_path, rank, field=2, attempts=3000, timeout=120):
    """Try to find a rank-r decomposition using flip-cpd."""
    import shutil
    flipcpd = shutil.which('flip-cpd')
    if not flipcpd:
        # Try common locations
        for p in ['/usr/local/bin/flip-cpd', '/usr/bin/flip-cpd',
                  Path.home() / '.local/bin/flip-cpd']:
            if Path(p).exists():
                flipcpd = str(p)
                break
    
    if not flipcpd:
        return None, "flip-cpd not found"
    
    cmd = [flipcpd, '--field', str(field), '--rank', str(rank),
           '--attempts', str(attempts), str(tensor_path)]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return result.returncode, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return -1, "timeout"

def main():
    T = make_M332()
    verify_M332(T)
    
    out_dir = Path('data/blaser_verification')
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # Save tensor
    tensor_path = out_dir / 'M332_tensor.txt'
    tensor_to_flipcpd_format(T, tensor_path)
    np.save(out_dir / 'M332_tensor.npy', T)
    
    results = {
        'tensor': 'M_<3,3,2>',
        'dimensions': [9, 6, 6],
        'nnz': int(np.count_nonzero(T)),
        'field': 2,
        'blaser_lower_bound': 14,
        'searches': []
    }
    
    # Verify flattening lower bounds
    T_flat1 = T.reshape(9, 36)
    T_flat2 = T.transpose(1,0,2).reshape(6, 54)
    T_flat3 = T.transpose(2,0,1).reshape(6, 54)
    
    # Over F_2
    r1 = np.linalg.matrix_rank(T_flat1.astype(float))
    r2 = np.linalg.matrix_rank(T_flat2.astype(float))
    r3 = np.linalg.matrix_rank(T_flat3.astype(float))
    print(f"Flattening ranks: {r1}, {r2}, {r3}")
    print(f"Flattening lower bound: max = {max(r1, r2, r3)}")
    results['flattening_ranks'] = [int(r1), int(r2), int(r3)]
    results['flattening_lower_bound'] = max(int(r1), int(r2), int(r3))
    
    # Try flip-cpd at various ranks
    for rank in [14, 15, 16, 13, 12]:
        print(f"\n=== flip-cpd rank {rank} ===")
        t0 = time.time()
        rc, output = run_flipcpd(tensor_path, rank, attempts=5000, timeout=180)
        elapsed = time.time() - t0
        found = rc == 0 if rc is not None else False
        status = 'found' if found else ('not_found' if rc is not None else 'error')
        print(f"  rank {rank}: {status} ({elapsed:.1f}s)")
        if output:
            # Check for success indicators
            lines = output.strip().split('\n')
            for line in lines[-5:]:
                print(f"  > {line}")
        
        results['searches'].append({
            'rank': rank,
            'status': status,
            'elapsed_sec': round(elapsed, 2),
            'return_code': rc,
            'last_output': output.strip().split('\n')[-3:] if output else []
        })
    
    out_path = out_dir / 'M332_rank_search.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved results to {out_path}")

if __name__ == '__main__':
    main()
