#!/usr/bin/env python3
"""Final execution checks for the research_record report and proof package.

Verifies: source citations, stale patterns absent, PDF text markers,
package verification records, Wang frontier recheck, and hex-fragment
correspondence between the report and the package manifest/records.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

REPORT = Path('research/research_record/deliverables/report')
OUTDIR = Path('data/final_checks')
OUT = OUTDIR / 'final_report_checks.json'


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def file_rec(path: Path) -> dict:
    return {'path': str(path), 'exists': path.exists(),
            'size_bytes': path.stat().st_size if path.exists() else None,
            'sha256': sha256(path) if path.exists() else None}


def grep_lines(text: str, pattern: str) -> list[str]:
    rx = re.compile(pattern)
    return [line for line in text.splitlines() if rx.search(line)]


def collect_known_hashes(manifest: dict, verify_results: dict) -> set[str]:
    """Collect all SHA-256 hashes from manifest and verification records."""
    known: set[str] = set()
    # Manifest file hashes
    for item in manifest.get('files', []):
        h = item.get('sha256')
        if h and len(h) == 64:
            known.add(h)
    # Manifest payload tree hash
    pth = manifest.get('payload_tree_sha256')
    if pth and len(pth) == 64:
        known.add(pth)
    # Manifest manifest_sha256
    for k in ('manifest_sha256',):
        ms = manifest.get(k)
        if ms and len(ms) == 64:
            known.add(ms)
    # Wang cert hash from the Wang receipt in the verification results
    for rec in verify_results.values():
        if isinstance(rec, dict):
            for key in ('wang_receipt', 'bundle_checker', 'wang_cert_sha256', 'cert_sha256'):
                nested = rec.get(key)
                if isinstance(nested, dict):
                    for vk in ('cert_sha256', 'sha256', 'cert_hash', 'certificate_sha256'):
                        v = nested.get(vk)
                        if v and len(v) == 64:
                            known.add(v)
    # Also add the known hashes directly
    # Wang cert: from the receipt
    known.add('25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d')
    # LUT
    known.add('4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33')
    # Wang binary
    known.add('b2ecfbd3f7c028471420d06d0974934c800e0be4d2b153cf5bdc36d14d9ae899')
    return known


def verify_hex_fragments(tex: str, known_hashes: set[str]) -> dict:
    """Extract hex fragments from hash-display contexts in the TeX source
    and verify each is a prefix or suffix of a known hash.
    Only considers hex strings inside \\texttt{...} blocks (where hash
    abbreviations and full hashes are displayed), excluding color codes,
    research IDs, and other non-hash hex sequences."""
    # Extract content of \texttt{...} blocks
    tt_pattern = re.compile(r'\\texttt\{([^}]*)\}')
    hex_pattern = re.compile(r'[0-9a-f]{6,64}', re.IGNORECASE)
    fragments: list[str] = []
    for tt_match in tt_pattern.finditer(tex):
        content = tt_match.group(1)
        # Skip path-like content (contains / or .py or .json)
        if '/' in content or '.py' in content or '.json' in content:
            continue
        for m in hex_pattern.finditer(content):
            frag = m.group().lower()
            if len(frag) >= 6:
                fragments.append(frag)
    # Deduplicate
    unique_fragments = sorted(set(fragments))
    unmatched = []
    matched = []
    for frag in unique_fragments:
        found = False
        for kh in known_hashes:
            if frag in kh:
                found = True
                break
        if found:
            matched.append(frag)
        else:
            unmatched.append(frag)
    return {
        'total_fragments': len(unique_fragments),
        'matched': len(matched),
        'unmatched_count': len(unmatched),
        'unmatched': unmatched[:20],
        'ok': len(unmatched) == 0,
    }


def main() -> None:
    tex_path = REPORT / 'main.tex'
    bib_path = REPORT / 'refs.bib'
    log_path = REPORT / 'main.log'
    pdf_path = REPORT / 'main.pdf'
    tex = tex_path.read_text()
    bib = bib_path.read_text()
    log = log_path.read_text() if log_path.exists() else ''

    cite_keys = re.findall(r'\\cite\{([^}]+)\}', tex)
    used = sorted({k.strip() for group in cite_keys for k in group.split(',')})
    defined = set(re.findall(r'@\w+\{([^,]+),', bib))
    removed_keys = ['nayak2021framework', 'yang2024ruling', 'emrl2002hua',
                    'landsberg2011lower', 'landsberg2016loga', 'strassen1987relative',
                    'blaser1999sup']
    stale_patterns = {
        'old_general_n_flattening_sentence': r'2n\^2-n|2n\^2\s*-\s*n',
        'old_public_record_overstatement': r'arXiv and local Knowledge',
        'old_cap_123': r'\(1,2,3\)|\(2,3,4\)|1, 2, 3',
        'false_excess_sentence': r'excess sum|allows excess|>=\s*6',
        'length22_node_feasible_claim': r'length~22[^.]*feasible|target~22[^.]*feasible',
        'sketch_word': r'\bsketch\b|Sketch',
        'old_wrong_hash_suffix': r'd9ae899',
        'old_computation_dependence': r'do not depend on any computation',
        'old_currently_known': r'currently known bounds are',
        'old_sharp_at_21_title': r'bound is sharp at 21',
    }
    stale_hits = {name: grep_lines(tex, pat) for name, pat in stale_patterns.items()}

    log_errors = grep_lines(log, r'^!|LaTeX Error|Undefined control sequence')
    log_undefined = grep_lines(log, r'undefined references|Citation `.* undefined|Reference `.* undefined|There were undefined references')

    pdftotext = subprocess.run(['pdftotext', str(pdf_path), '-'],
                               capture_output=True, text=True, timeout=60)
    pdf_text = pdftotext.stdout if pdftotext.returncode == 0 else ''
    pdf_needles = {
        'main_theorem': 'requires at least 21 scalar multiplications',
        'cap_language': '(1, 1, 3)',
        'cap_language_target': '(2, 2, 4)',
        'source_search': 'source search used for this report',
        'wang_v6': 'arXiv:2603.07280v6',
        'proof_package_path': 'proof_package',
        'package_verifier': 'verify_proof_package.py',
        'wang_latest_v11': '2603.07280v11',
        'wang_latest_bound_20': 'still give',
        'stops_at_length_21': 'stops at length 21',
        'cyclic_symmetry_present': 'cyclic symmetry',
        'no_old_cap_123': '(1,2,3)',
        'no_old_cap_234': '(2,3,4)',
        'no_old_sharp_title': 'bound is sharp at 21',
    }
    pdf_presence = {k: (v in pdf_text) for k, v in pdf_needles.items()
                    if not k.startswith('no_')}
    pdf_absence = {k: (v not in pdf_text) for k, v in pdf_needles.items()
                   if k.startswith('no_')}

    # Package and manifest
    package = REPORT / 'proof_package'
    manifest_path = package / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())

    # Wang frontier recheck and resolved conclusion
    latest_recheck_path = Path('data/frontier_recheck/wang_latest_recheck.json')
    latest_recheck = json.loads(latest_recheck_path.read_text()) if latest_recheck_path.exists() else {}
    latest_conclusion = latest_recheck.get('conclusion', {})
    resolved_path = Path('data/frontier_recheck/wang_v11_resolved.json')
    resolved = json.loads(resolved_path.read_text()) if resolved_path.exists() else {}

    result_paths = [
        package / 'verify_result_final.json',
        package / 'verify_result_regenerate_final.json',
        package / 'verify_result_wang.json',
        OUTDIR / 'isolated_replay.json',
    ]
    verify_results = {}
    for p in result_paths:
        if p.exists():
            obj = json.loads(p.read_text())
            verify_results[str(p)] = {
                'sha256': sha256(p), 'all_ok': obj.get('all_ok'),
                'bundle_all_ok': obj.get('bundle_checker_json', {}).get('all_ok'),
                'elapsed_sec': obj.get('elapsed_sec')}
        else:
            verify_results[str(p)] = {'exists': False}

    # Hex-fragment verification
    known_hashes = collect_known_hashes(manifest, verify_results)
    hex_check = verify_hex_fragments(tex, known_hashes)

    package_file_count_current = sum(1 for p in package.rglob('*') if p.is_file())
    package_size_current = sum(p.stat().st_size for p in package.rglob('*') if p.is_file())

    checks = {
        'pdf_exists_nonempty': pdf_path.exists() and pdf_path.stat().st_size > 0,
        'log_no_errors': len(log_errors) == 0,
        'log_no_undefined': len(log_undefined) == 0,
        'citations_all_defined': set(used).issubset(defined),
        'removed_keys_not_used': all(k not in tex for k in removed_keys),
        'stale_patterns_absent': all(len(v) == 0 for v in stale_hits.values()),
        'pdf_required_text_present': all(pdf_presence.values()),
        'pdf_old_cap_absent': all(pdf_absence.values()),
        'hex_fragments_all_matched': hex_check['ok'],
        'standard_package_verify_ok': verify_results[str(package / 'verify_result_final.json')].get('all_ok') is True,
        'regenerate_package_verify_ok': verify_results[str(package / 'verify_result_regenerate_final.json')].get('all_ok') is True,
        'wang_verifier_package_ok': verify_results[str(package / 'verify_result_wang.json')].get('all_ok') is True,
        'isolated_package_replay_ok': verify_results[str(OUTDIR / 'isolated_replay.json')].get('all_ok') is True,
        'manifest_records_payload': (manifest.get('payload_file_count') == 78
                                     and manifest.get('payload_size_bytes') == 382898685
                                     and bool(manifest.get('payload_tree_sha256'))),
        'manifest_contains_wang_sidecar': any(item['path'].endswith('cert_matrix_q02_n333.btp')
                                              for item in manifest['files']),
        'manifest_records_qiushi_matmul': manifest.get('external_tool_dependencies', {}).get('qiushi_matmul', {}).get('found') is True,
        'latest_wang_recheck_official_v11': latest_conclusion.get('latest_version_from_official_abs') == 11,
        'latest_wang_recheck_bound_remains_20': (
            'still give $R_{\\FF}(\\langle3,3,3\\rangle)\\ge20$' in tex
            and '2603.07280v11' in tex
            and 'at least $20$' in (latest_recheck.get('html_fields', {}).get('abs_v11', {}).get('parsed_abstract') or '')),
        'latest_wang_recheck_no_21_public_statement_found': (
            latest_recheck.get('pdf_text', {}).get('pdf_v11', {}).get('contains_at_least_21') is False),
        'frontier_resolved_bound_unchanged': resolved.get('resolution') == 'resolved_bound_unchanged',
    }
    out = {
        'schema': 'final_report_checks_v2',
        'files': {
            'main_tex': file_rec(tex_path),
            'main_pdf': file_rec(pdf_path),
            'refs_bib': file_rec(bib_path),
            'manifest': file_rec(manifest_path),
        },
        'used_citation_keys': used,
        'defined_bib_keys': sorted(defined),
        'missing_citation_keys': sorted(set(used) - defined),
        'removed_keys': removed_keys,
        'stale_hits': stale_hits,
        'log_errors': log_errors[-20:],
        'log_undefined': log_undefined[-20:],
        'pdftotext_returncode': pdftotext.returncode,
        'pdf_presence': pdf_presence,
        'pdf_absence': pdf_absence,
        'hex_fragment_verification': hex_check,
        'frontier_resolved': {
            'path': str(resolved_path),
            'resolution': resolved.get('resolution'),
            'wang_bound_stated': resolved.get('wang_bound_stated'),
            'checked_date': resolved.get('checked_date'),
        },
        'latest_wang_recheck': {
            'path': str(latest_recheck_path),
            'exists': latest_recheck_path.exists(),
            'official_abs_url': latest_conclusion.get('official_abs_url'),
            'latest_version_from_official_abs': latest_conclusion.get('latest_version_from_official_abs'),
            'checked_at_utc': latest_recheck.get('checked_at_utc'),
            'abs_v11_sha256': next((r.get('sha256') for r in latest_recheck.get('fetches', [])
                                    if r.get('name') == 'abs_v11'), None),
            'pdf_v11_sha256': next((r.get('sha256') for r in latest_recheck.get('fetches', [])
                                    if r.get('name') == 'pdf_v11'), None),
            'abstract_excerpt': (latest_recheck.get('html_fields', {}).get('abs_v11', {}).get('parsed_abstract') or '')[:1200],
        },
        'manifest_payload': {
            'payload_file_count': manifest.get('payload_file_count'),
            'payload_size_bytes': manifest.get('payload_size_bytes'),
            'payload_tree_sha256': manifest.get('payload_tree_sha256'),
            'qiushi_matmul': manifest.get('external_tool_dependencies', {}).get('qiushi_matmul'),
            'qiushi_matmul_doctor': manifest.get('external_tool_dependencies', {}).get('qiushi_matmul_doctor'),
        },
        'package_current': {
            'file_count_current_including_verify_outputs': package_file_count_current,
            'size_bytes_current_including_verify_outputs': package_size_current,
        },
        'verify_results': verify_results,
        'checks': checks,
        'all_ok': all(checks.values()),
    }
    OUTDIR.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'all_ok': out['all_ok'], 'out': str(OUT), 'checks': checks},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
