#!/usr/bin/env python3
"""End-to-end checker for the analysis lower-bound certificate bundle.

This is not a solver search.  It independently checks the certificate inputs that
support the current proof of R_F2(T_333) >= 21:

  * Wang certificate receipt/hash and expanded LUT hash;
  * dim-1 LUT values all equal 19;
  * the load-bearing dim-2 all-high-rank orbits are exactly 484--491;
  * for each of 484--491, independently rebuild the target-18 node-local
    occupation rows, regenerate the Boolean-copy CNF, compare SHA256 to the
    stored CNF, and run drat-trim on the stored DRAT proof;
  * normalized column-coset hyperplanes: one rank-one family has LB 15 and the
    fourteen affine planes have LB 17;
  * AG(3,2) cap number is 4;
  * saved algebra/transpose/coset verification records exist and are positive.

The checker deliberately uses the independent analysis row/CNF reconstruction
rather than the older node-local row builder.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pickle
import shutil
import subprocess
import sys
import tempfile
import time
from itertools import combinations
from pathlib import Path
from typing import Iterable, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from dim2_independent_semantics import (  # type: ignore
    LUT_PATH, CACHE_PATH, rref_ind, pack_ind, independent_rows, popcount, file_sha256
)
from dim2_cnf_cert import build_cnf_for_orbit  # type: ignore

SESSION = Path("research/research_record")
VERIFY_RECEIPT = Path("data/wang_f2_lb20/verify_receipt.json")
WANG_CERT = Path("data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt")
CERT_DIR = Path("data/dim2_cnf_cert_all")
INDEP_SUMMARY = Path("data/dim2_independent/independent_semantics_summary.json")
ORBIT491_T19 = Path("data/dim2_independent/orbit491_target19_long.json")
TRANSPOSE_JSON = Path("data/audit/transpose_convention.json")
SATURATION_JSON = Path("data/audit/saturation_proof.json")
GL3_JSON = Path("data/audit/gl3_invariance.json")
COSET_JSON = Path("data/audit/coset_lemma.json")
AG32_JSON = Path("data/audit/ag32_cap.json")
OUT = Path("data/bundle_check/bundle_check.json")

INDICES = [484,485,486,487,488,489,490,491]
EXPECTED_WANG_CERT_SHA = "25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d"
EXPECTED_LUT_SHA = "4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33"


def bits_to_mat(x: int):
    return [[(int(x) >> (3*i+j)) & 1 for j in range(3)] for i in range(3)]


def gf2_rank_bits(x: int) -> int:
    rows = []
    for i in range(3):
        r = 0
        for j in range(3):
            if (int(x) >> (3*i+j)) & 1:
                r |= 1 << j
        rows.append(r)
    basis = []
    for v0 in rows:
        v = v0
        for b in basis:
            p = b.bit_length()-1
            if p >= 0 and ((v>>p)&1):
                v ^= b
        if v:
            p = v.bit_length()-1
            for ii,b in enumerate(basis):
                if (b>>p)&1:
                    basis[ii] = b ^ v
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def span_nonzero(basis: Sequence[int]) -> list[int]:
    out = []
    for c in range(1, 1 << len(basis)):
        v = 0
        for i,b in enumerate(basis):
            if (c>>i)&1:
                v ^= int(b)
        out.append(v)
    return sorted(set(out))


def rref_any(rows: Iterable[int], nbits: int = 9) -> Tuple[int,...]:
    return rref_ind(tuple(rows), nbits)


def load_lut_cache():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    return lut, cache


def check_wang_receipt() -> dict:
    receipt = json.loads(VERIFY_RECEIPT.read_text())
    cert_sha = file_sha256(WANG_CERT)
    return {
        'receipt_path': str(VERIFY_RECEIPT),
        'receipt_status': receipt.get('status'),
        'claimed_lower_bound': receipt.get('claimed_lower_bound'),
        'receipt_certificate_sha256': receipt.get('certificate_sha256'),
        'actual_certificate_sha256': cert_sha,
        'ok': receipt.get('status') == 'verified' and receipt.get('claimed_lower_bound') == 20 and receipt.get('certificate_sha256') == EXPECTED_WANG_CERT_SHA and cert_sha == EXPECTED_WANG_CERT_SHA,
    }


def check_dim1_and_dim2(lut, cache) -> dict:
    dim1_vals = []
    for a in range(1,512):
        key = pack_ind(rref_any([a]))
        dim1_vals.append(lut.get(key))
    orbits = {int(o['cert_index']): o for o in cache['orbits'] if int(o['dim']) == 2}
    rank_patterns = {}
    all_high = []
    for idx,o in sorted(orbits.items()):
        W = rref_any([int(x) for x in o['basis']])
        ranks = sorted(gf2_rank_bits(v) for v in span_nonzero(W))
        rank_patterns[idx] = ranks
        if min(ranks) >= 2:
            all_high.append(idx)
    return {
        'dim1_count': len(dim1_vals),
        'dim1_value_hist': {str(v): dim1_vals.count(v) for v in sorted(set(dim1_vals))},
        'dim1_all_19': all(v == 19 for v in dim1_vals),
        'dim2_rank_patterns_478_491': {str(i): rank_patterns.get(i) for i in range(478,492)},
        'all_high_dim2_indices': all_high,
        'all_high_exact_484_491': all_high == INDICES,
        'raw_lb_484_491': {str(i): int(orbits[i]['raw_lb']) for i in INDICES},
        'ok': all(v == 19 for v in dim1_vals) and all_high == INDICES and all(int(orbits[i]['raw_lb']) == 18 for i in INDICES),
    }


def check_drat_bundle(regenerate: bool, drat_timeout: int) -> dict:
    drat_trim = shutil.which('drat-trim')
    if drat_trim is None:
        return {'ok': False, 'error': 'drat-trim not found'}
    results = []
    t0 = time.time()
    for idx in INDICES:
        rec_path = CERT_DIR / f'orbit_{idx}' / f'orbit_{idx}_target_18_certificate.json'
        rec = json.loads(rec_path.read_text())
        item = {
            'cert_index': idx,
            'record_path': str(rec_path),
            'record_exists': rec_path.exists(),
            'record_cnf_sha256': rec.get('cnf_sha256'),
            'record_proof_sha256': rec.get('cadical',{}).get('proof_sha256'),
            'record_drat_verified': rec.get('drat_trim',{}).get('verified'),
            'cnf_path': rec.get('cnf_path'),
            'proof_path': rec.get('cadical',{}).get('proof_path'),
        }
        cnf = Path(rec['cnf_path']); proof = Path(rec['cadical']['proof_path'])
        item['actual_cnf_sha256'] = file_sha256(cnf)
        item['actual_proof_sha256'] = file_sha256(proof)
        item['hashes_match_record'] = (item['actual_cnf_sha256'] == item['record_cnf_sha256'] and item['actual_proof_sha256'] == item['record_proof_sha256'])

        # Independently rebuild rows and check row digest.
        lut, cache = load_lut_cache()
        orb = next(o for o in cache['orbits'] if int(o['cert_index']) == idx)
        W = rref_any([int(x) for x in orb['basis']])
        rows, meta = independent_rows(W, lut, 18)
        item['independent_row_digest'] = meta['row_digest']
        item['record_row_digest'] = rec.get('row_meta',{}).get('row_digest')
        item['row_digest_matches'] = item['independent_row_digest'] == item['record_row_digest']
        item['independent_row_count'] = len(rows)

        if regenerate:
            with tempfile.TemporaryDirectory(prefix=f'q_orbit_{idx}_') as td:
                tmp = Path(td)
                rebuilt = build_cnf_for_orbit(idx, 18, tmp, False, 0, 0)
                item['regenerated_cnf_sha256'] = rebuilt['cnf_sha256']
                item['regenerated_cnf_matches'] = rebuilt['cnf_sha256'] == item['actual_cnf_sha256']
                item['regenerated_cnf_vars'] = rebuilt['cnf_variables']
                item['regenerated_cnf_clauses'] = rebuilt['cnf_clauses']
        else:
            item['regenerated_cnf_matches'] = None

        cmd = [drat_trim, str(cnf), str(proof)]
        tt = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=drat_timeout)
        item['drat_trim_returncode'] = proc.returncode
        item['drat_trim_elapsed_sec'] = time.time() - tt
        item['drat_trim_verified_now'] = proc.returncode == 0 and ('VERIFIED' in proc.stdout or 'VERIFIED' in proc.stderr)
        item['drat_trim_stdout_tail'] = proc.stdout[-1000:]
        item['ok'] = item['hashes_match_record'] and item['row_digest_matches'] and item['drat_trim_verified_now'] and (item['regenerated_cnf_matches'] is not False)
        results.append(item)
    return {'results': results, 'elapsed_sec': time.time()-t0, 'all_ok': all(x['ok'] for x in results), 'ok': all(x['ok'] for x in results)}


def affine_planes_f2_3() -> list[tuple[int,...]]:
    planes = set()
    nonzero_dirs = [1,2,3,4,5,6,7]
    # A 2-dim linear direction is generated by two independent vectors.
    dir_planes = set()
    for a,b in combinations(nonzero_dirs,2):
        if a != b:
            D = tuple(sorted([0,a,b,a^b]))
            if len(set(D)) == 4:
                dir_planes.add(D)
    for D in dir_planes:
        for x in range(8):
            planes.add(tuple(sorted(x ^ d for d in D)))
    return sorted(planes)


def check_coset_planes(lut) -> dict:
    # Normalized S from analysis: <272,4,2,1>.  R=<4,2,1> is rank-one family.
    p = 272
    row_basis = [1,2,4]
    S = rref_any([p] + row_basis)
    S_lb = lut.get(pack_ind(S))
    values = []
    R = rref_any(row_basis)
    R_key = pack_ind(R)
    R_lb = lut.get(R_key)
    # Hyperplanes of S: kernels of nonzero linear functionals on coefficient labels.
    # Basis order [p,1,2,4] for labels x=(x0,x1,x2,x3).  Hyperplane with dual d
    # contains vectors whose coefficient dot product with d is zero.
    basis = [p,1,2,4]
    hypers = []
    for dual in range(1,16):
        rows = []
        for coeff in range(1,16):
            if (coeff & dual).bit_count() % 2 == 0:
                v = 0
                for i,b in enumerate(basis):
                    if (coeff>>i)&1:
                        v ^= b
                rows.append(v)
        H = rref_any(rows)
        lb = lut.get(pack_ind(H))
        # Count how many affine coset elements p + e1*w are in H.
        coset_count = 0
        labels = []
        for w in range(8):
            v = p ^ sum(((w>>i)&1) * row_basis[i] for i in range(3))
            # in span H?
            if rref_any(list(H)+[v]) == tuple(H):
                coset_count += 1; labels.append(w)
        hypers.append({'dual': dual, 'basis': list(H), 'lb': lb, 'coset_count': coset_count, 'labels': labels})
        values.append(lb)
    affine = [h for h in hypers if h['basis'] != list(R)]
    return {
        'S_basis': list(S),
        'S_lb': S_lb,
        'R_basis': list(R),
        'R_lb': R_lb,
        'hyperplane_lb_hist': {str(v): values.count(v) for v in sorted(set(values))},
        'affine_plane_count': len(affine),
        'affine_plane_lb_hist': {str(v): [h['lb'] for h in affine].count(v) for v in sorted(set(h['lb'] for h in affine))},
        'affine_planes_all_lb_17': len(affine) == 14 and all(h['lb'] == 17 and h['coset_count'] == 4 for h in affine),
        'rank_one_family_lb_15': R_lb == 15,
        'ok': S_lb == 14 and R_lb == 15 and len(affine) == 14 and all(h['lb'] == 17 and h['coset_count'] == 4 for h in affine),
        'hyperplanes': hypers,
    }


def check_ag32() -> dict:
    planes = affine_planes_f2_3()
    cap_free = []
    for S in combinations(range(8),5):
        if not any(set(P).issubset(S) for P in planes):
            cap_free.append(S)
    no_plane_4 = [S for S in combinations(range(8),4) if not any(set(P).issubset(S) for P in planes)]
    return {'n_planes': len(planes), 'every_5_has_plane': len(cap_free)==0, 'no_plane_4_count': len(no_plane_4), 'cap_number': 4 if len(cap_free)==0 and len(no_plane_4)>0 else None, 'ok': len(planes)==14 and len(cap_free)==0 and len(no_plane_4)>0}


def check_saved_records() -> dict:
    checks = {}
    for name,path,predicate in [
        ('independent_semantics', INDEP_SUMMARY, lambda o: o.get('all_rows_match_existing') and o.get('all_target18_infeasible') and o.get('all_projected_rank23_controls_pass')),
        ('orbit491_target19', ORBIT491_T19, lambda o: o.get('solve',{}).get('feasible') is True and o.get('solve',{}).get('violations_check') == 0),
        ('transpose', TRANSPOSE_JSON, lambda o: o.get('tensor_symmetric_under_correct_auto') is True and o.get('conv2_failures_ATC_B') == 0),
        ('saturation', SATURATION_JSON, lambda o: o.get('P_is_permutation') is True and o.get('P_rank') == 27 and o.get('formula_ok') is True and o.get('diagonal_ok') is True and o.get('offdiag_all_rank3') is True),
        ('gl3', GL3_JSON, lambda o: o.get('gl3_transitive_on_vectors') is True and o.get('invariance_failures') == 0),
        ('coset', COSET_JSON, lambda o: o.get('lemma_verified') is True and o.get('h4_neither') == 0),
        ('ag32_saved', AG32_JSON, lambda o: o.get('every_5_has_plane') is True and o.get('n_4_planes') == 14),
    ]:
        if not path.exists():
            checks[name] = {'path': str(path), 'exists': False, 'ok': False}
            continue
        obj = json.loads(path.read_text())
        ok = bool(predicate(obj))
        checks[name] = {'path': str(path), 'exists': True, 'sha256': file_sha256(path), 'ok': ok}
    return {'records': checks, 'ok': all(v['ok'] for v in checks.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, default=OUT)
    ap.add_argument('--regenerate-cnf', action='store_true', help='Regenerate all eight CNFs and compare hashes.')
    ap.add_argument('--drat-timeout', type=int, default=900)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    lut, cache = load_lut_cache()
    result = {'schema': 'lower_bound_bundle_check_v1', 'started_at': time.time()}
    result['wang_receipt'] = check_wang_receipt()
    result['lut_hash'] = {'path': str(LUT_PATH), 'sha256': file_sha256(LUT_PATH), 'ok': file_sha256(LUT_PATH)==EXPECTED_LUT_SHA}
    result['cache_hash'] = {'path': str(CACHE_PATH), 'sha256': file_sha256(CACHE_PATH)}
    result['dim1_dim2'] = check_dim1_and_dim2(lut, cache)
    result['coset_planes'] = check_coset_planes(lut)
    result['ag32'] = check_ag32()
    result['saved_records'] = check_saved_records()
    result['drat_bundle'] = check_drat_bundle(args.regenerate_cnf, args.drat_timeout)
    result['finished_at'] = time.time()
    result['elapsed_sec'] = result['finished_at'] - result['started_at']
    result['all_ok'] = all([
        result['wang_receipt']['ok'], result['lut_hash']['ok'], result['dim1_dim2']['ok'],
        result['coset_planes']['ok'], result['ag32']['ok'], result['saved_records']['ok'],
        result['drat_bundle']['ok'],
    ])
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'elapsed_sec': result['elapsed_sec'],
        'all_ok': result['all_ok'],
        'drat_all_ok': result['drat_bundle']['ok'],
        'regenerate_cnf': args.regenerate_cnf,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
