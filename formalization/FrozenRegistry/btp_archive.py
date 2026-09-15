"""Inspect pinned BTP v2 traces and their prerequisites; not a Lean rank proof.

Codec and DFS order follow the public pinned upstream core/backtracking_proof.cc
and verifier/backtracking_verifier.h. No orbit or certificate search is performed.
"""

import argparse
from collections import Counter
from functools import lru_cache
import gzip
import hashlib
import io
import json
from pathlib import Path
import struct

from certificate_metadata import read_metadata
from generate_certificate import rref


ARCHIVE_SHA256 = '4e824eb13c235e69045881d173d8ababe622421055a238005afce413aabe3289'
ARCHIVE_BYTES = 33013656
CERTIFICATE_SHA256 = '25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d'


class Archive:
    def __init__(self, data):
        self.data = data
        if len(data) < 20:
            raise ValueError('truncated BTP header')
        magic, version, count = struct.unpack_from('<8sIQ', data)
        if magic != b'BTPARCH\0' or version != 2:
            raise ValueError('expected BTPARCH version 2 (hydrate any Git LFS pointer)')
        if count > (len(data) - 20) // 8:
            raise ValueError('truncated BTP slot table')
        self.slots = []
        pos = 20
        for _ in range(count):
            if pos + 8 > len(data):
                raise ValueError('truncated BTP slot length')
            length, = struct.unpack_from('<Q', data, pos)
            pos += 8
            if pos + length > len(data):
                raise ValueError('truncated BTP slot')
            self.slots.append((pos, length))
            pos += length
        if pos != len(data):
            raise ValueError('trailing bytes after BTP slots')

    def blob(self, index):
        if not 0 <= index < len(self.slots):
            raise ValueError('BTP slot index out of range')
        pos, length = self.slots[index]
        return self.data[pos:pos + length]

    def leaf_count(self, index):
        blob = self.blob(index)
        if not blob:
            return 0
        with gzip.GzipFile(fileobj=io.BytesIO(blob)) as stream:
            header = stream.read(8)
        if len(header) != 8:
            raise ValueError('truncated BTP proof header')
        count, = struct.unpack('<Q', header)
        if not count:
            raise ValueError('nonempty BTP slot encodes an empty proof')
        return count

    def records(self, index, leaf_limit):
        count = self.leaf_count(index)
        if count > leaf_limit:
            raise ValueError(f'trace has {count} leaves, above explicit limit {leaf_limit}')
        if not count:
            return []
        expected = 8 + 13 * count
        with gzip.GzipFile(fileobj=io.BytesIO(self.blob(index))) as stream:
            body = stream.read(expected + 1)
        if len(body) != expected:
            raise ValueError('BTP proof body length disagrees with its leaf count')
        return [(body[8 + i],
                 struct.unpack_from('<I', body, 8 + count + 4 * i)[0],
                 struct.unpack_from('<I', body, 8 + 5 * count + 4 * i)[0],
                 struct.unpack_from('<I', body, 8 + 9 * count + 4 * i)[0])
                for i in range(count)]


@lru_cache(maxsize=None)
def product(a, b):
    return sum((sum(((a >> (3 * i + k)) & 1) * ((b >> (3 * k + j)) & 1)
                    for k in range(3)) % 2) << (3 * i + j)
               for i in range(3) for j in range(3))


def transpose(a):
    return sum(((a >> (3 * i + j)) & 1) << (3 * j + i)
               for i in range(3) for j in range(3))


@lru_cache(maxsize=None)
def inverse(a):
    if not 0 <= a < 512:
        raise ValueError('matrix code out of range')
    result = next((b for b in range(512) if product(a, b) == 273), None)
    if result is None or product(result, a) != 273:
        raise ValueError('singular witness matrix')
    return result


@lru_cache(maxsize=None)
def witness_units(query, store):
    left, flip = query & 65535, query >> 16
    if flip not in (0, 1):
        raise ValueError('invalid transpose flag')
    inverse(left)
    right = inverse(store)
    return tuple(product(product(left, transpose(1 << k) if flip else 1 << k), right)
                 for k in range(9))


def canonical_image(basis, query, store):
    units = witness_units(query, store)
    images = []
    for code in basis:
        value = 0
        for k, unit in enumerate(units):
            if code >> k & 1:
                value ^= unit
        images.append(value)
    return rref(images)


def lean_transport(basis, query, store):
    """Invert the archive action in generate_certificate's checked-transport format.

    Archive: canonical = L * transpose^flip(actual) * R^-1.
    Lean: actual = P^T * transpose^flip(canonical) * Qinv^T.
    These are exact images, not a reversal of source-span containment.
    """
    witness_units(query, store)
    left, flip = query & 65535, bool(query >> 16)
    if flip:
        p, q, qi = store, left, inverse(left)
    else:
        p, q, qi = transpose(inverse(left)), transpose(inverse(store)), transpose(store)
    pairs = []
    for code in basis:
        preimage = product(product(left, transpose(code) if flip else code), inverse(store))
        actual = product(product(transpose(p), transpose(preimage) if flip else preimage),
                         transpose(qi))
        if actual != code:
            raise ValueError('archive witness inversion disagrees with Lean action')
        pairs.append([code, preimage])
    return dict(P=p, Q=q, Qinv=qi, flip=flip, pairs=pairs)


def trace_dependencies(row, records, rows):
    """Replay finite trace structure/witness arithmetic, using numeric labels only.

    This identifies required rank interfaces. It deliberately does not turn the
    numeric labels or a successful Python replay into proved rank bounds.
    """
    basis, lower = row['basis'], row['lb']
    if tuple(basis) != rref(basis) or not 0 < lower <= 32:
        raise ValueError('invalid base RREF or lower bound')
    pivots = sum(1 << (c.bit_length() - 1) for c in basis)
    minimal = [c for c in range(1, 512) if not c & pivots]
    by_basis = {tuple(r['basis']): r for r in rows}
    if not minimal or len(by_basis) != len(rows):
        raise ValueError('empty quotient or duplicate frozen bases')
    cursor, path = 0, []
    dependencies = Counter()
    required = {}
    witnesses = {}

    def visit(max_index):
        nonlocal cursor
        if cursor >= len(records):
            raise ValueError('DFS exhausted the trace before all children closed')
        depth, mask, query, store = records[cursor]
        if not 0 < depth < lower or len(path) > depth:
            raise ValueError('invalid leaf depth or DFS ordering')
        if len(path) == depth:
            if mask <= 0 or mask >> depth or not mask & (1 << (depth - 1)):
                raise ValueError('invalid leaf mask or newest entry not selected')
            selected = [c for i, c in enumerate(path) if mask >> i & 1]
            extended = rref([*basis, *selected])
            canonical = canonical_image(extended, query, store)
            source = by_basis.get(canonical)
            needed = lower - mask.bit_count()
            if source is None or len(canonical) <= len(basis):
                raise ValueError('leaf does not reach a larger frozen source space')
            if source['lb'] < needed:
                raise ValueError('leaf source label too weak')
            source_id = source['index']
            dependencies[source_id] += 1
            required[source_id] = max(needed, required.get(source_id, 0))
            key = (extended, query, store)
            witnesses.setdefault(key, dict(basis=list(extended), source_id=source_id,
                                          query_elem=query, store_elem=store))
            cursor += 1
            return
        if len(path) >= lower - 1:
            raise ValueError('DFS did not close by decomposition length')
        for i in range(max_index + 1):
            path.append(minimal[i])
            visit(i)
            path.pop()

    visit(len(minimal) - 1)
    if cursor != len(records):
        raise ValueError('unconsumed BTP records')
    for witness in witnesses.values():
        witness['lean_transport'] = lean_transport(witness['basis'], witness['query_elem'],
                                                  witness['store_elem'])
    return dict(leaves=cursor, depth_min=min(r[0] for r in records),
                depth_max=max(r[0] for r in records),
                prerequisites=[dict(index=i, required_bound=required[i],
                                    frozen_bound=rows[i]['lb'], leaves=dependencies[i])
                               for i in sorted(dependencies)],
                witnesses=list(witnesses.values()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--registry', type=Path, required=True)
    parser.add_argument('--node', type=int, action='append', default=[])
    parser.add_argument('--leaf-limit', type=int, default=100000)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = args.archive.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != ARCHIVE_SHA256 or len(data) != ARCHIVE_BYTES:
        raise ValueError('archive differs from the public pinned LFS object')
    archive = Archive(data)
    metadata = read_metadata(args.certificate)
    if metadata['certificate_sha256'] != CERTIFICATE_SHA256:
        raise ValueError('certificate differs from the public pinned protobuf input')
    rows = metadata['rows']
    if len(archive.slots) != len(rows):
        raise ValueError('archive slot count differs from frozen table')
    registry = json.loads(args.registry.read_text())
    known = {r['index']: r for r in registry['entries']}
    for index, entry in known.items():
        if any(entry[k] != rows[index][k] for k in ('index', 'basis', 'lb')):
            raise ValueError('registry entry differs from frozen table')
    counts = [archive.leaf_count(i) for i in range(len(rows))]
    for row, count in zip(rows, counts):
        if count != row.get('proof_size', 0):
            raise ValueError('archive trace length differs from protobuf metadata')
    remaining = sorted(set(range(len(rows))) - known.keys())
    result = dict(archive_sha256=digest, archive_bytes=len(data),
                  certificate_sha256=metadata['certificate_sha256'],
                  registry_sha256=hashlib.sha256(args.registry.read_bytes()).hexdigest(),
                  slots=len(counts), nonempty_traces=sum(bool(n) for n in counts),
                  remaining_trace_count=sum(bool(counts[i]) for i in remaining),
                  remaining_trace_leaves=sum(counts[i] for i in remaining),
                  remaining_without_trace=[i for i in remaining if not counts[i]],
                  trace_sizes={str(i): n for i, n in enumerate(counts) if n}, nodes=[])
    for index in args.node:
        if not 0 <= index < len(rows):
            raise ValueError('node index out of range')
        row = rows[index]
        if not counts[index] or counts[index] > args.leaf_limit:
            result['nodes'].append(dict(index=index, status='not_decoded',
                                        proof_type=row['proof_type'], leaves=counts[index]))
            continue
        decoded = trace_dependencies(row, archive.records(index, args.leaf_limit), rows)
        decoded.update(index=index, basis=row['basis'], lower=row['lb'],
                       status='python_trace_structure_and_witnesses_checked')
        for source in decoded['prerequisites']:
            source['registered'] = source['index'] in known
        result['nodes'].append(decoded)
        print(json.dumps({k: v for k, v in decoded.items() if k != 'witnesses'}), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('nodes', 'trace_sizes')}))


if __name__ == '__main__':
    main()
