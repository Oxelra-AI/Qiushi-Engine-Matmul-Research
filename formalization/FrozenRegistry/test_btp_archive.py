"""Codec and trace-reuse tests; no Python result is a rank theorem."""

import gzip
import hashlib
import os
from pathlib import Path
import struct
import unittest

from btp_archive import (ARCHIVE_BYTES, ARCHIVE_SHA256, CERTIFICATE_SHA256, Archive,
                         canonical_image, inverse, lean_transport, product, read_metadata,
                         rref, trace_dependencies, transpose)


def proof_body(records):
    n = len(records)
    return (struct.pack('<Q', n) + bytes(r[0] for r in records) +
            b''.join(struct.pack('<' + str(n) + 'I', *(r[j] for r in records))
                     for j in range(1, 4)))


def archive_bytes(blobs):
    return (struct.pack('<8sIQ', b'BTPARCH\0', 2, len(blobs)) +
            b''.join(struct.pack('<Q', len(b)) + b for b in blobs))


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.records = [(1, 1, 273, 273), (1, 1, 273, 273), (1, 1, 273, 273)]
        self.data = archive_bytes([b'', gzip.compress(proof_body(self.records), mtime=0)])
        base = [256, 128, 64, 32, 16, 8, 4]
        self.rows = [dict(index=0, basis=base, lb=2)] + [
            dict(index=i, basis=list(rref([*base, i])), lb=1) for i in range(1, 4)]

    def test_arrays_round_trip_and_empty_slot(self):
        archive = Archive(self.data)
        self.assertEqual(archive.leaf_count(0), 0)
        self.assertEqual(archive.records(0, 3), [])
        self.assertEqual(archive.leaf_count(1), 3)
        self.assertEqual(archive.records(1, 3), self.records)
        with self.assertRaisesRegex(ValueError, 'explicit limit'):
            archive.records(1, 2)

    def test_header_and_slot_corruption(self):
        for bad in (b'', self.data[:12], self.data[:-1], self.data + b'x',
                    b'wrong!!!' + self.data[8:], self.data[:8] + b'\x03' + self.data[9:]):
            with self.subTest(length=len(bad)), self.assertRaises(ValueError):
                Archive(bad)
        with self.assertRaisesRegex(ValueError, 'index out of range'):
            Archive(self.data).blob(-1)

    def test_body_length_and_empty_proof_rejected(self):
        for body in (proof_body(self.records)[:-1], proof_body(self.records) + b'x',
                     struct.pack('<Q', 0)):
            with self.assertRaises(ValueError):
                Archive(archive_bytes([gzip.compress(body)])).records(0, 3)

    def test_dfs_coverage_and_actual_witnesses(self):
        result = trace_dependencies(self.rows[0], self.records, self.rows)
        self.assertEqual(result['leaves'], 3)
        self.assertEqual([r['index'] for r in result['prerequisites']], [1, 2, 3])
        self.assertEqual([r['required_bound'] for r in result['prerequisites']], [1, 1, 1])

    def test_missing_extra_and_invalid_leaves(self):
        bad_records = [self.records[:-1], self.records + self.records[:1]]
        bad_records += [[bad, *self.records[1:]] for bad in
                        [(0, 1, 273, 273), (2, 1, 273, 273),
                         (1, 0, 273, 273), (1, 2, 273, 273),
                         (1, 1, 0, 273), (1, 1, 273, 0)]]
        for records in bad_records:
            with self.subTest(records=records), self.assertRaises(ValueError):
                trace_dependencies(self.rows[0], records, self.rows)

    def test_missing_and_weak_source_rejected(self):
        with self.assertRaisesRegex(ValueError, 'larger frozen source'):
            trace_dependencies(self.rows[0], self.records, self.rows[:-1])
        weak = [*self.rows[:1], dict(self.rows[1], lb=0), *self.rows[2:]]
        with self.assertRaisesRegex(ValueError, 'source label too weak'):
            trace_dependencies(weak[0], self.records, weak)

    def test_inverses_transpose_and_nonidentity(self):
        for code in [273, 161, 473, 244]:
            inv = inverse(code)
            self.assertEqual(product(code, inv), 273)
            self.assertEqual(product(inv, code), 273)
        self.assertEqual(canonical_image([2], 273 + (1 << 16), 273), (8,))
        for left, right in [(161, 473), (244, 161)]:
            for code in range(512):
                self.assertEqual(canonical_image([product(product(inverse(left), code), right)],
                                                 left, right), rref([code]))
        with self.assertRaisesRegex(ValueError, 'transpose flag'):
            canonical_image([1], 273 + (2 << 16), 273)

    def test_explicit_lean_transport_both_directions(self):
        for left, right in [(273, 273), (161, 473), (244, 161)]:
            for flip in (False, True):
                result = lean_transport(list(range(512)), left + (int(flip) << 16), right)
                self.assertEqual(product(result['Q'], result['Qinv']), 273)
                self.assertEqual(product(result['Qinv'], result['Q']), 273)
                inverse(result['P'])
                for actual, canonical in result['pairs']:
                    self.assertEqual(canonical, product(product(left,
                        transpose(actual) if flip else actual), inverse(right)))
                    self.assertEqual(actual, product(product(transpose(result['P']),
                        transpose(canonical) if flip else canonical), transpose(result['Qinv'])))

    @unittest.skipUnless(os.environ.get('BTP_ARCHIVE'), 'set BTP_ARCHIVE for pinned input check')
    def test_pinned_archive_and_short_dependencies(self):
        data = Path(os.environ['BTP_ARCHIVE']).read_bytes()
        self.assertEqual(len(data), ARCHIVE_BYTES)
        self.assertEqual(hashlib.sha256(data).hexdigest(), ARCHIVE_SHA256)
        archive = Archive(data)
        certificate = Path(__file__).resolve().parents[2] / (
            'proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt')
        metadata = read_metadata(certificate)
        self.assertEqual(metadata['certificate_sha256'], CERTIFICATE_SHA256)
        rows = metadata['rows']
        self.assertEqual(len(archive.slots), 496)
        self.assertEqual(sum(bool(archive.leaf_count(i)) for i in range(496)), 238)
        for row in rows:
            self.assertEqual(archive.leaf_count(row['index']), row.get('proof_size', 0))
        for index, sources in [(24, [5, 7, 9]), (27, [7, 8, 9]), (28, [9]),
                               (33, [5, 11, 13]), (410, [248, 249])]:
            result = trace_dependencies(rows[index], archive.records(index, 1000), rows)
            self.assertEqual([r['index'] for r in result['prerequisites']], sources)


if __name__ == '__main__':
    unittest.main()
