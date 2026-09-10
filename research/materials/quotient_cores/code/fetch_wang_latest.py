#!/usr/bin/env python3
"""Fetch and inspect the latest official arXiv version of Wang 2603.07280.

This is a final frontier-framing check for the research_record report.  The proof
package uses the pinned v6 certificate; the public-priority statement depends
on whether the current arXiv version already states a 3x3/F2 rank-21 lower
bound.
"""
from __future__ import annotations

import hashlib
import html
import json
import re
import subprocess
import time
import urllib.request
from pathlib import Path

OUT = Path('data/frontier_recheck')
OUT.mkdir(parents=True, exist_ok=True)
UA = {'User-further research': 'QiushiDiscovery/1.0 final-frontier-check'}
URLS = {
    'abs_latest': 'https://arxiv.org/abs/2603.07280',
    'abs_v11': 'https://arxiv.org/abs/2603.07280v11',
    'pdf_latest': 'https://arxiv.org/pdf/2603.07280',
    'pdf_v11': 'https://arxiv.org/pdf/2603.07280v11',
}

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def fetch(name: str, url: str) -> dict:
    suffix = '.pdf' if '/pdf/' in url else '.html'
    path = OUT / f'{name}{suffix}'
    rec = {'name': name, 'url': url, 'path': str(path), 'ok': False}
    try:
        req = urllib.request.Request(url, headers=UA)
        with urllib.request.urlopen(req, timeout=120) as r:
            data = r.read()
            path.write_bytes(data)
            rec.update({
                'ok': True,
                'status': getattr(r, 'status', None),
                'content_type': r.headers.get('content-type'),
                'size_bytes': len(data),
                'sha256': hashlib.sha256(data).hexdigest(),
            })
    except Exception as e:
        rec['error'] = repr(e)
    return rec

def extract_html_fields(path: Path) -> dict:
    text = path.read_text('utf-8', errors='replace')
    def meta(prop: str) -> str | None:
        m = re.search(r'<meta[^>]+(?:property|name)=["\']' + re.escape(prop) + r'["\'][^>]+content=["\'](.*?)["\']', text, flags=re.S)
        if not m:
            m = re.search(r'<meta[^>]+content=["\'](.*?)["\'][^>]+(?:property|name)=["\']' + re.escape(prop) + r'["\']', text, flags=re.S)
        return html.unescape(re.sub(r'\s+', ' ', m.group(1)).strip()) if m else None
    title_m = re.search(r'<h1[^>]*class=["\']title[^>]*>\s*<span[^>]*>Title:\s*</span>\s*(.*?)\s*</h1>', text, flags=re.S)
    abs_m = re.search(r'<blockquote[^>]*class=["\']abstract[^>]*>\s*<span[^>]*>Abstract:\s*</span>\s*(.*?)\s*</blockquote>', text, flags=re.S)
    dateline_m = re.search(r'<div class="dateline">(.*?)</div>', text, flags=re.S)
    version_links = re.findall(r'href="/abs/2603\.07280v(\d+)"', text)
    return {
        'og_url': meta('og:url'),
        'og_title': meta('og:title'),
        'og_description': meta('og:description'),
        'parsed_title': html.unescape(re.sub(r'<[^>]+>', '', title_m.group(1))).strip() if title_m else None,
        'parsed_abstract': html.unescape(re.sub(r'\s+', ' ', re.sub(r'<[^>]+>', ' ', abs_m.group(1))).strip()) if abs_m else None,
        'dateline': html.unescape(re.sub(r'\s+', ' ', re.sub(r'<[^>]+>', ' ', dateline_m.group(1))).strip()) if dateline_m else None,
        'version_numbers_seen_in_links': sorted({int(v) for v in version_links}),
        'raw_head': text[:2000],
    }

def pdf_to_text(pdf_path: Path) -> dict:
    out_text = OUT / (pdf_path.stem + '.txt')
    rec = {'pdf': str(pdf_path), 'text_path': str(out_text)}
    try:
        cp = subprocess.run(['pdftotext', str(pdf_path), str(out_text)], capture_output=True, text=True, timeout=120)
        rec.update({'returncode': cp.returncode, 'stdout': cp.stdout, 'stderr': cp.stderr})
        if out_text.exists():
            txt = out_text.read_text('utf-8', errors='replace')
            rec.update({'text_size': len(txt), 'text_sha256': sha256(out_text)})
            # Context snippets around load-bearing phrases.
            patterns = [
                r'3\s*[×x]\\?\s*3|3\\times 3|3 × 3',
                r'at least\s+20', r'at least\s+21', r'lower bounds? for three small formats',
                r'Bl[aä]ser', r'<3,\s*3,\s*3>|⟨3,\s*3,\s*3⟩', r'3,3,3',
            ]
            snippets = []
            for pat in patterns:
                for m in re.finditer(pat, txt, flags=re.I):
                    s = max(0, m.start() - 350)
                    e = min(len(txt), m.end() + 650)
                    snippets.append({'pattern': pat, 'start': m.start(), 'snippet': re.sub(r'\s+', ' ', txt[s:e]).strip()})
                    if len([x for x in snippets if x['pattern'] == pat]) >= 8:
                        break
            rec['snippets'] = snippets[:80]
            rec['contains_at_least_20_3x3_abstract'] = ('3 × 3' in txt or '3 x 3' in txt or '3\\times 3' in txt) and ('at least 20' in txt)
            rec['contains_at_least_21'] = bool(re.search(r'at least\s+21', txt, flags=re.I))
            rec['contains_rank_21_near_333'] = bool(re.search(r'(3\s*[×x,]\\?\s*3.{0,500}(at least\s+21|>=\s*21|≥\s*21))|((at least\s+21|>=\s*21|≥\s*21).{0,500}3\s*[×x,]\\?\s*3)', txt, flags=re.I|re.S))
    except Exception as e:
        rec['error'] = repr(e)
    return rec

def main() -> None:
    checked_at = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    fetches = [fetch(n,u) for n,u in URLS.items()]
    html_fields = {}
    for rec in fetches:
        p = Path(rec['path'])
        if rec.get('ok') and p.suffix == '.html':
            html_fields[rec['name']] = extract_html_fields(p)
    pdf_text = {}
    for rec in fetches:
        p = Path(rec['path'])
        if rec.get('ok') and p.suffix == '.pdf':
            pdf_text[rec['name']] = pdf_to_text(p)
    # Direct conclusion from official abstract and extracted PDF text.
    latest = html_fields.get('abs_latest') or {}
    latest_url = latest.get('og_url') or ''
    latest_version = None
    m = re.search(r'2603\.07280v(\d+)', latest_url)
    if m:
        latest_version = int(m.group(1))
    abstract = latest.get('og_description') or latest.get('parsed_abstract') or ''
    f2_333_lower_bound_abstract = None
    if re.search(r'3\s*(?:\\times|×|x)\s*3.{0,160}F}_?2|3\s*(?:\\times|×|x)\s*3.{0,160}F_2|F}_?2.{0,160}3\s*(?:\\times|×|x)\s*3|F_2.{0,160}3\s*(?:\\times|×|x)\s*3', abstract, flags=re.I|re.S):
        if re.search(r'at least\s*20', abstract, flags=re.I):
            f2_333_lower_bound_abstract = 20
        if re.search(r'at least\s*21', abstract, flags=re.I):
            f2_333_lower_bound_abstract = 21
    all_text = '\n'.join([abstract] + [Path(v['text_path']).read_text('utf-8', errors='replace') for v in pdf_text.values() if Path(v['text_path']).exists()])
    conclusion = {
        'latest_version_from_official_abs': latest_version,
        'official_abs_url': latest_url,
        'abstract_says_f2_3x3_at_least_20': bool(re.search(r'3\s*(?:\\times|×|x)\s*3.{0,250}at least\s*20|at least\s*20.{0,250}3\s*(?:\\times|×|x)\s*3', abstract, flags=re.I|re.S)),
        'abstract_says_f2_3x3_at_least_21': bool(re.search(r'3\s*(?:\\times|×|x)\s*3.{0,250}at least\s*21|at least\s*21.{0,250}3\s*(?:\\times|×|x)\s*3', abstract, flags=re.I|re.S)),
        'pdf_text_contains_at_least_21_anywhere': bool(re.search(r'at least\s*21', all_text, flags=re.I)),
        'pdf_text_contains_21_near_333': bool(re.search(r'(3\s*(?:\\times|×|x|,)\s*3.{0,700}(at least\s*21|>=\s*21|≥\s*21))|((at least\s*21|>=\s*21|≥\s*21).{0,700}3\s*(?:\\times|×|x|,)\s*3)', all_text, flags=re.I|re.S)),
        'frontier_recheck_result': 'latest_official_arxiv_v11_abstract_still_states_f2_3x3_lower_bound_at_least_20_no_21_statement_found' if latest_version == 11 and bool(re.search(r'3\s*(?:\\times|×|x)\s*3.{0,250}at least\s*20|at least\s*20.{0,250}3\s*(?:\\times|×|x)\s*3', abstract, flags=re.I|re.S)) and not bool(re.search(r'3\s*(?:\\times|×|x|,)\s*3.{0,700}(at least\s*21|>=\s*21|≥\s*21)|((at least\s*21|>=\s*21|≥\s*21).{0,700}3\s*(?:\\times|×|x|,)\s*3)', all_text, flags=re.I|re.S)) else 'needs_verification',
    }
    out = {
        'schema': 'wang_latest_frontier_recheck_v1',
        'checked_at_utc': checked_at,
        'fetches': fetches,
        'html_fields': html_fields,
        'pdf_text': pdf_text,
        'conclusion': conclusion,
    }
    (OUT / 'wang_latest_recheck.json').write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(OUT / 'wang_latest_recheck.json'), **conclusion}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
