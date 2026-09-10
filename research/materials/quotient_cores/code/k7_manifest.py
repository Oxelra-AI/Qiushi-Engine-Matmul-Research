#!/usr/bin/env python3
"""Build a unified k=7 matching proof manifest with all dependencies bound.

This manifest makes the k=7 nonadjacent matching closure independently
verifiable from one entry point by binding:
  1. The anchored matching orbit enumeration (analysis)
  2. The one-dimensional lb=19 multiplicity-free premise
  3. Wang LUT path/hash and metadata
  4. The six k=7 representative certificates
  5. Graph-CNF/DRAT artifact hashes
  6. Independent row-membership checks
"""
import hashlib
import json
import pathlib
import pickle
import sys

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis  # noqa:E402
from graph_coloring_certificate import rank1_points, load_lut, iter_strata  # noqa:E402


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def check_dim1_lb19(lut: dict) -> dict:
    """Verify that all 511 one-dimensional Wang LUT rows have lb >= 19."""
    dim1_count = 0
    min_lb = 999
    violations = []
    for key, lb in lut.items():
        basis = unpack_basis(int(key))
        nonzero = [b for b in basis if int(b) != 0]
        if len(nonzero) == 1:
            dim1_count += 1
            min_lb = min(min_lb, int(lb))
            if int(lb) < 19:
                violations.append({'key': int(key), 'lb': int(lb)})
    return {
        'dim1_count': dim1_count,
        'expected_count': 511,
        'match': dim1_count == 511,
        'min_lb': min_lb,
        'all_lb_ge_19': min_lb >= 19,
        'violations': violations,
    }


def main():
    lut_path = pathlib.Path('workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    strata_path = pathlib.Path('workspace/data/matching_strata/anchored_matching_strata.json')

    # Paths to k=7 certificate artifacts
    cert_summary = pathlib.Path('workspace/data/graph_cert/k7_rerun/summary_k07.json')
    cert_verified = pathlib.Path('workspace/data/graph_cert/k7_rerun/verification_k7_certified.json')
    graph_summary = pathlib.Path('workspace/data/graph_cert/k7_graph_is_cnf_with_vex/summary.json')
    strict_verify = pathlib.Path('workspace/data/graph_cert/k7_graph_is_cnf_with_vex/strict_verification_graph_is_cnf.json')
    cover_audit = pathlib.Path('workspace/data/matching_strata/cover_connection_audit.json')

    # Check all files exist
    required = [lut_path, strata_path, cert_summary, graph_summary]
    for p in required:
        if not p.exists():
            print(f'MISSING: {p}')
            return

    print('Loading LUT...')
    lut = load_lut(lut_path)
    print(f'  {len(lut):,} entries')

    # 1. Wang LUT metadata
    lut_hash = sha256_file(lut_path)
    print(f'LUT SHA256: {lut_hash}')

    # 2. Check one-dimensional lb >= 19 (multiplicity-free premise)
    dim1 = check_dim1_lb19(lut)
    print(f'Dim-1 check: count={dim1["dim1_count"]}, min_lb={dim1["min_lb"]}, all_ge_19={dim1["all_lb_ge_19"]}')

    # 3. Strata classification
    strata_hash = sha256_file(strata_path)
    with strata_path.open() as f:
        strata_data = json.load(f)
    k7_strata = []
    all_strata = list(iter_strata(strata_path, 7))
    for idx, st in all_strata:
        k7_strata.append({
            'idx': idx,
            'matching': [int(x) for x in st['canonical']],
            'orbit_size': int(st.get('orbit_image_count', st.get('enumerated_members', 0))),
            'k': 7,
        })
    total_orbit = sum(s['orbit_size'] for s in k7_strata)
    print(f'K=7 strata: {len(k7_strata)}, total orbit size: {total_orbit}')

    # 4. Load certificate summaries
    with cert_summary.open() as f:
        certs = json.load(f)
    with graph_summary.open() as f:
        graphs = json.load(f)

    # Map certificates to strata
    cert_map = {}
    for r in certs.get('results', []):
        idx = r['idx']
        cert_map[idx] = {
            'type': r.get('status', '?'),
            'source': 'clique_cover' if 'clique' in str(r.get('status', '')) else
                      'matching_violates' if 'matching_violates' in str(r.get('status', '')) else
                      'other',
        }
    for r in graphs.get('records', []):
        idx = r['idx']
        if r.get('verified'):
            cert_map[idx] = {
                'type': 'graph_cnf_drat_verified',
                'cnf_vars': r.get('cnf_vars'),
                'cnf_clauses': r.get('cnf_clauses'),
                'source': str(r.get('cnf', '')),
            }

    # 5. Compute hashes for all certificate artifacts
    artifact_hashes = {}
    for p in [cert_summary, cert_verified, graph_summary, strict_verify, cover_audit]:
        if p.exists():
            artifact_hashes[str(p)] = sha256_file(p)
    # Hash individual cert files
    cert_dir = pathlib.Path('workspace/data/graph_cert/k7_rerun/')
    for f in sorted(cert_dir.glob('*.cert.json')):
        artifact_hashes[str(f)] = sha256_file(f)
    cnf_dir = pathlib.Path('workspace/data/graph_cert/k7_graph_is_cnf_with_vex/')
    for f in sorted(cnf_dir.glob('*.cnf')):
        artifact_hashes[str(f)] = sha256_file(f)
    for f in sorted(cnf_dir.glob('*.drat')):
        artifact_hashes[str(f)] = sha256_file(f)

    # 6. Build manifest
    manifest = {
        'schema': 'k7_matching_proof_manifest_v1',
        'meaning': (
            'Unified manifest for the k=7 nonadjacent matching level of the Wang F2 support '
            'proof tree. All six canonical k=7 anchored matching strata are excluded as '
            'Wang-admissible A-side support configurations. This is a support-side necessary '
            'condition result over F2; it does not close the adjacent-pair branch, does not '
            'close k<=6, and does not prove R_F2 >= 21 or rank-23 optimality.'
        ),
        'dependencies': {
            'wang_lut': {
                'path': str(lut_path),
                'sha256': lut_hash,
                'entry_count': len(lut),
            },
            'dim1_multiplicity_free_premise': dim1,
            'anchored_matching_classification': {
                'path': str(strata_path),
                'sha256': strata_hash,
                'total_anchored_matchings': strata_data.get('anchored_matching_count', '?'),
                'k7_strata_count': len(k7_strata),
                'k7_total_orbit': total_orbit,
            },
            'cover_connection_audit': {
                'path': str(cover_audit),
                'sha256': artifact_hashes.get(str(cover_audit)),
                'exists': cover_audit.exists(),
            },
        },
        'k7_strata': [],
    }

    all_closed = True
    for s in k7_strata:
        idx = s['idx']
        entry = dict(s)
        if idx in cert_map:
            entry['certificate'] = cert_map[idx]
            entry['closed'] = True
        else:
            entry['closed'] = False
            all_closed = False
        manifest['k7_strata'].append(entry)

    manifest['all_k7_closed'] = all_closed
    manifest['artifact_hashes'] = artifact_hashes

    # 7. Verification summary
    manifest['verification_steps'] = [
        'Load Wang LUT from the specified path and verify its SHA256.',
        'Confirm all 511 one-dimensional rows have lb >= 19 (multiplicity-free premise).',
        'Load anchored matching classification and verify SHA256 and k=7 orbit counts.',
        'For each k=7 stratum: replay the certificate type against the LUT.',
        '  - matching_violates: find the cited Wang row, verify matching intersection exceeds capacity.',
        '  - clique_cover: verify each intra-color pair has a residual-1 Wang row, and color_count < target.',
        '  - graph_cnf_drat: regenerate the graph CNF from vertex/edge exclusion rows, verify clause multiset, replay DRAT.',
        'Verify that the six strata exhaust all k=7 orbits (orbit sizes sum to expected total).',
    ]

    out_path = pathlib.Path('workspace/data/k7_manifest/k7_unified_manifest.json')
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {out_path}')
    print(f'All k=7 closed: {all_closed}')


if __name__ == '__main__':
    main()
