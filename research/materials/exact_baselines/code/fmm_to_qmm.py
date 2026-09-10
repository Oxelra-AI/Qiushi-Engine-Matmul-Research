#!/usr/bin/env python3
"""Convert FastMatrixMultiplication JSON schemes to QMM_SCHEME_V1 format.

Handles two FMM JSON layouts:
  1. Dense: u/v/w are lists of dense integer vectors (serendipitous_base, naive_*)
  2. Sparse: u/v/w are lists of [{"index":i,"value":v},...] (addition_reduced, etc.)

For the addition-reduced format, only the "fresh" raw factor representation
can be directly used; the combined `u` uses intermediate-variable indices
beyond the raw dimension.  We reconstruct from the symbolic 'multiplications'
field when present, or from the raw dense u/v/w arrays when they are
9-dimensional.
"""
import argparse, json, re, sys
from pathlib import Path


def is_dense_vec(v, dim):
    return isinstance(v, list) and len(v) == dim and all(isinstance(x, (int, float)) for x in v)


def sparse_to_dense(sv, dim):
    out = [0] * dim
    for entry in sv:
        idx = entry['index']
        val = entry['value']
        if idx >= dim:
            return None  # index beyond raw dimension
        out[idx] = val
    return out


def parse_symbolic_multiplications(mults, n):
    """Parse 'multiplications' list like 'm1 = (expr_a) * (expr_b)' into (u, v) vectors.
    Returns (u_list, v_list) each of length len(mults), each entry a list of dim elements.
    Does NOT parse w (output assignments); those come from 'elements' or w array.
    """
    dim_a = n[0] * n[1]  # 9 for 3x3
    dim_b = n[1] * n[2]  # 9 for 3x3

    # Map aIJ -> index in row-major A, bIJ -> index in row-major B
    a_map = {}
    b_map = {}
    for i in range(n[0]):
        for j in range(n[1]):
            a_map[f'a{i+1}{j+1}'] = i * n[1] + j
    for i in range(n[1]):
        for j in range(n[2]):
            b_map[f'b{i+1}{j+1}'] = i * n[2] + j

    u_list = []
    v_list = []
    for m in mults:
        # Parse: mN = (expr_a) * (expr_b)
        match = re.match(r'm\d+\s*=\s*\((.+?)\)\s*\*\s*\((.+?)\)', m)
        if not match:
            return None, None
        expr_a, expr_b = match.group(1).strip(), match.group(2).strip()
        u = [0] * dim_a
        v = [0] * dim_b
        for tok in re.findall(r'[+-]?\s*\d*\s*[ab]\d{2}', expr_a.replace(' ', '')):
            tok = tok.replace(' ', '')
            m2 = re.match(r'([+-]?)(\d*)([ab]\d{2})', tok)
            if not m2:
                continue
            sign = -1 if m2.group(1) == '-' else 1
            coeff = int(m2.group(2)) if m2.group(2) else 1
            var = m2.group(3)
            if var in a_map:
                u[a_map[var]] += sign * coeff
        for tok in re.findall(r'[+-]?\s*\d*\s*[ab]\d{2}', expr_b.replace(' ', '')):
            tok = tok.replace(' ', '')
            m2 = re.match(r'([+-]?)(\d*)([ab]\d{2})', tok)
            if not m2:
                continue
            sign = -1 if m2.group(1) == '-' else 1
            coeff = int(m2.group(2)) if m2.group(2) else 1
            var = m2.group(3)
            if var in b_map:
                v[b_map[var]] += sign * coeff
        u_list.append(u)
        v_list.append(v)
    return u_list, v_list


def transpose_w(w_vec, n1, n3):
    """Transpose w vector from FMM column-major to QMM row-major indexing.
    
    FMM stores w for C^T: w[n1*k + i] = coeff for C_{ik}.
    QMM expects row-major: w[n3*i + k] = coeff for C_{ik}.
    So we reshape as (n3, n1), transpose to (n1, n3), and flatten.
    """
    import numpy as np
    return np.array(w_vec).reshape(n3, n1).T.flatten().tolist()


def convert_fmm_json(data, source_name='unknown'):
    """Convert FMM JSON to QMM dict: {dimensions, rank, domain, terms}.
    
    NOTE: FMM stores w in column-major (C^T) indexing.
    We transpose w to row-major to match the QMM verifier convention.
    """
    n = data['n']
    m = data['m']
    dim_a = n[0] * n[1]
    dim_b = n[1] * n[2]
    dim_c = n[0] * n[2]
    n1, n2, n3 = n[0], n[1], n[2]

    # Try dense u/v/w first
    u_raw, v_raw, w_raw = data.get('u', []), data.get('v', []), data.get('w', [])

    if len(u_raw) == m and is_dense_vec(u_raw[0], dim_a):
        # Dense format
        terms = []
        for i in range(m):
            w_fixed = transpose_w(w_raw[i], n1, n3)
            terms.append({
                'index': i,
                'u': [int(x) for x in u_raw[i]],
                'v': [int(x) for x in v_raw[i]],
                'w': [int(x) for x in w_fixed],
            })
        domain = 'integer'
        for t in terms:
            for k in ['u', 'v', 'w']:
                for x in t[k]:
                    if not isinstance(x, int) or x != int(x):
                        domain = 'rational'
        if data.get('z2'):
            domain = 'F2'
        return {'dimensions': tuple(n), 'rank': m, 'domain': domain, 'terms': terms}

    # Try sparse format
    if len(u_raw) == m and isinstance(u_raw[0], list) and len(u_raw[0]) > 0 and isinstance(u_raw[0][0], dict):
        all_ok = True
        terms = []
        for i in range(m):
            u = sparse_to_dense(u_raw[i], dim_a)
            v = sparse_to_dense(v_raw[i], dim_b)
            w = sparse_to_dense(w_raw[i], dim_c)
            if u is None or v is None or w is None:
                all_ok = False
                break
            w = transpose_w(w, n1, n3)
            terms.append({'index': i, 'u': u, 'v': v, 'w': [int(x) for x in w]})
        if all_ok:
            return {'dimensions': tuple(n), 'rank': m, 'domain': 'integer', 'terms': terms}

    # Try symbolic multiplications for u,v; w from dense array
    if 'multiplications' in data:
        u_list, v_list = parse_symbolic_multiplications(data['multiplications'], n)
        if u_list and len(u_list) == m:
            # w must come from dense w array
            if len(w_raw) == m and is_dense_vec(w_raw[0], dim_c):
                terms = []
                for i in range(m):
                    terms.append({
                        'index': i,
                        'u': u_list[i],
                        'v': v_list[i],
                        'w': [int(x) for x in w_raw[i]],
                    })
                return {'dimensions': tuple(n), 'rank': m, 'domain': 'integer', 'terms': terms}

    return None


def write_qmm(qmm, outpath):
    """Write QMM_SCHEME_V1 file."""
    lines = ['QMM_SCHEME_V1']
    d = qmm['dimensions']
    lines.append(f'dimensions {d[0]} {d[1]} {d[2]}')
    lines.append(f'rank {qmm["rank"]}')
    lines.append(f'domain {qmm["domain"]}')
    lines.append('index_order row-major')
    for t in qmm['terms']:
        lines.append(f'term {t["index"]}')
        lines.append('u ' + ' '.join(str(x) for x in t['u']))
        lines.append('v ' + ' '.join(str(x) for x in t['v']))
        lines.append('w ' + ' '.join(str(x) for x in t['w']))
    Path(outpath).write_text('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('json_input', help='FMM JSON file')
    ap.add_argument('--output', '-o', required=True, help='Output .qmm file')
    args = ap.parse_args()

    data = json.loads(Path(args.json_input).read_text())
    qmm = convert_fmm_json(data, source_name=args.json_input)
    if qmm is None:
        print(f'ERROR: could not convert {args.json_input}', file=sys.stderr)
        sys.exit(1)

    write_qmm(qmm, args.output)
    print(json.dumps({
        'status': 'ok',
        'output': args.output,
        'dimensions': qmm['dimensions'],
        'rank': qmm['rank'],
        'domain': qmm['domain'],
    }))


if __name__ == '__main__':
    main()
