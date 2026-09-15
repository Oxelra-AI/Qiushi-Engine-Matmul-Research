"""Pinned-trace translation regressions; Lean remains the proof checker."""

import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest

from btp_archive import Archive, read_metadata
from btp_to_lean import (check_source_imports, checked_root_certificate, emit, emit_tests,
                         root_farkas_certificate, root_rows, singleton_cover_certificate, translate)


@unittest.skipUnless(os.environ.get('BTP_ARCHIVE'), 'set BTP_ARCHIVE for trace translation tests')
class TranslationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        cls.archive = Archive(Path(os.environ['BTP_ARCHIVE']).read_bytes())
        cls.rows = read_metadata(cls.root.parent / (
            'proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt'))['rows']
        cls.registry = json.loads((cls.root / 'FrozenRegistry/checked.json').read_text())
        cls.records = cls.archive.records(227, 1000)
        cls.translated = translate(cls.rows[227], cls.records, cls.rows, cls.registry)

    def test_source_closure_and_branch_accounting(self):
        meta, cert, ledger, transports = self.translated
        self.assertEqual((meta['n_live'], meta['n_occ']), (15, 15))
        self.assertEqual(sorted(int(k) for k in ledger['entries']), [47, 48, 57, 60, 61, 68, 78, 83])
        self.assertEqual(set(transports), set(range(15)))
        self.assertEqual(len(cert['branch']['certs']), 520)
        paths = {leaf['path'] for leaf in cert['branch']['certs']}
        self.assertEqual(len(paths), 520)
        self.assertTrue(all(leaf['rhs'] < 0 for leaf in cert['branch']['certs']))
        visited = set()

        def visit(node, lower, upper):
            if node['type'] == 'leaf':
                visited.add(node['path'])
                leaf = next(leaf for leaf in cert['branch']['certs'] if leaf['path'] == node['path'])
                for q, value in leaf['lower'].items():
                    self.assertGreaterEqual(lower.get(int(q), 0), value)
                for q, value in leaf['upper'].items():
                    self.assertLessEqual(upper[int(q)], value)
                return
            q, floor = node['label'] - 1, node['floor']
            visit(node['left'], lower, upper | {q: floor})
            visit(node['right'], lower | {q: floor + 1}, upper)

        visit(cert['branch']['tree'], {}, {})
        self.assertEqual(visited, paths)

    def test_unregistered_or_weak_source_rejected(self):
        missing = dict(entries=[r for r in self.registry['entries'] if r['index'] != 47])
        with self.assertRaisesRegex(ValueError, 'unregistered rank prerequisite 47'):
            translate(self.rows[227], self.records, self.rows, missing)
        weak = copy.deepcopy(self.registry)
        next(r for r in weak['entries'] if r['index'] == 47)['source']['bound'] = 0
        with self.assertRaisesRegex(ValueError, 'bound too weak'):
            translate(self.rows[227], self.records, self.rows, weak)

    def test_corrupt_or_incomplete_trace_rejected(self):
        for records in (self.records[:-1], self.records + self.records[:1],
                        [(0, 1, 273, 273), *self.records[1:]]):
            with self.assertRaises(ValueError):
                translate(self.rows[227], records, self.rows, self.registry)

    def test_registry_aggregate_source_rejected(self):
        cyclic = copy.deepcopy(self.registry)
        next(r for r in cyclic['entries'] if r['index'] == 47)['source']['module'] = 'FrozenRegistry.Bindings'
        with self.assertRaisesRegex(ValueError, 'acyclic source'):
            translate(self.rows[227], self.records, self.rows, cyclic)

    def test_independent_and_cyclic_source_modules(self):
        for name in ('FrozenRegistry.Seed020', 'FrozenRegistry.TransportBindings',
                     'FrozenRegistry.Btp227Final'):
            check_source_imports(name, 265)
        with self.assertRaisesRegex(ValueError, 'acyclic source'):
            check_source_imports('FrozenRegistry.Btp227Final', 227)
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'FrozenRegistry').mkdir()
            adapter = root / 'FrozenRegistry/Adapter.lean'
            for imports in ('import FrozenRegistry.Bindings', 'import FrozenRegistry.Adapter'):
                adapter.write_text(imports + '\n')
                with self.assertRaisesRegex(ValueError, 'acyclic source'):
                    check_source_imports('FrozenRegistry.Adapter', 265, root)

    def test_orbit_adapter_source(self):
        meta, cert, ledger, _ = translate(self.rows[265], self.archive.records(265, 1000),
                                         self.rows, self.registry)
        self.assertEqual(meta['n_live'], 31)
        self.assertEqual(len(cert['branch']['certs']), 475)
        source = ledger['entries']['90']
        self.assertEqual(source['module'], 'FrozenRegistry.TransportBindings')
        self.assertEqual(source['theorem'], 'QiushiMatmul.FrozenRegistry.Transport.bound090')
        self.assertEqual(source['basis_codes'], self.rows[90]['basis'])

    def test_emitted_guards_use_actual_basis_and_bound(self):
        meta = self.translated[0]
        with tempfile.TemporaryDirectory() as folder:
            destination = Path(folder)
            emit_tests(meta, destination)
            text = (destination / 'Btp227Tests.lean').read_text()
            self.assertIn(f'frozenWangTable.basis 227 = {meta["basis"]}', text)
            self.assertIn('frozenWangTable.lower 227 = 15', text)
            self.assertIn('Lean.collectAxioms', text)
            self.assertIn('throwError "Unexpected axiom', text)

    def test_singleton_capacity_compression(self):
        meta, _, _, _ = translate(self.rows[265], self.archive.records(265, 1000),
                                  self.rows, self.registry)
        cert = singleton_cover_certificate(meta)
        self.assertEqual(len(cert['branch']['certs']), 1)
        leaf = cert['branch']['certs'][0]
        self.assertEqual(leaf['rhs'], -6)
        self.assertEqual(len(leaf['used_rows']), 32)
        missing = copy.deepcopy(meta)
        missing['source_rows'] = missing['source_rows'][1:]
        self.assertIsNone(singleton_cover_certificate(missing))
        weak = copy.deepcopy(meta)
        for row in weak['source_rows']:
            row['lb'] = 0
        self.assertIsNone(singleton_cover_certificate(weak))

    def test_source_only_retains_all_checked_source_interfaces(self):
        compact = translate(self.rows[227], self.records, self.rows, self.registry, source_only=True)
        for index in [0, 2, 3]:
            self.assertEqual(compact[index], self.translated[index])
        self.assertIsNone(compact[1])
        with self.assertRaises(ValueError):
            translate(self.rows[227], self.records[:-1], self.rows, self.registry, source_only=True)
        missing = dict(entries=[r for r in self.registry['entries'] if r['index'] != 47])
        with self.assertRaisesRegex(ValueError, 'unregistered rank prerequisite 47'):
            translate(self.rows[227], self.records, self.rows, missing, source_only=True)

    def test_root_farkas_exact_weights_and_rejections(self):
        meta, _, _, _ = translate(self.rows[265], self.archive.records(265, 1000),
                                  self.rows, self.registry, source_only=True)
        cert = root_farkas_certificate(meta)
        self.assertEqual(len(cert['branch']['certs']), 1)
        self.assertLess(cert['branch']['certs'][0]['rhs'], 0)
        _, _, refs = root_rows(meta)
        weights = [0] * len(refs)
        for item in cert['branch']['certs'][0]['used_rows']:
            ref = {k: v for k, v in item.items() if k != 'multiplier'}
            weights[refs.index(ref)] = item['multiplier']
        self.assertEqual(checked_root_certificate(meta, weights), cert)
        for bad in [weights[:-1], [-1, *weights[1:]], [0] * len(weights),
                    [float(w) for w in weights]]:
            with self.assertRaises(ValueError):
                checked_root_certificate(meta, bad)
        broken = list(weights)
        broken[refs.index(dict(type='total_ge'))] += 1
        with self.assertRaises(ValueError):
            checked_root_certificate(meta, broken)
        for row in meta['source_rows']:
            row['lb'] = 0
        self.assertIsNone(root_farkas_certificate(meta))

    @unittest.skipUnless(os.environ.get('CERTIFICATE_EMITTER'), 'set CERTIFICATE_EMITTER for regeneration')
    def test_sources_regenerate_identically_twice(self):
        spec = importlib.util.spec_from_file_location('emitter_fixture', os.environ['CERTIFICATE_EMITTER'])
        emitter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(emitter)
        with tempfile.TemporaryDirectory() as folder:
            staging, destination = Path(folder) / 'stage', Path(folder) / 'dest'
            for _ in range(2):
                count = emit(emitter, *self.translated, staging, destination)
                self.assertEqual(count, 81)
                for source in destination.glob('*.lean'):
                    self.assertEqual(source.read_bytes(),
                                     (self.root / 'FrozenRegistry' / source.name).read_bytes(), source.name)

    @unittest.skipUnless(os.environ.get('CERTIFICATE_EMITTER'), 'set CERTIFICATE_EMITTER for regeneration')
    def test_compression_discards_stale_staged_leaves(self):
        spec = importlib.util.spec_from_file_location('emitter_compact_fixture', os.environ['CERTIFICATE_EMITTER'])
        emitter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(emitter)
        meta, cert, ledger, transports = translate(self.rows[265], self.archive.records(265, 1000),
                                                  self.rows, self.registry)
        with tempfile.TemporaryDirectory() as folder:
            staging, destination = Path(folder) / 'stage', Path(folder) / 'dest'
            emit(emitter, meta, cert, ledger, transports, staging, destination)
            compact = singleton_cover_certificate(meta)
            emit(emitter, meta, compact, ledger, transports, staging, destination)
            self.assertEqual(len(list(staging.glob('Btp265Leaf[0-9]*.lean'))), 1)
            self.assertEqual(len(list(staging.glob('Btp265Leaves*.lean'))), 1)
            self.assertEqual(len(list(destination.glob('Btp265Leaves*.lean'))), 1)
            tree = (destination / 'Btp265Tree.lean').read_text()
            self.assertNotIn('by_cases', tree)
            self.assertIn('plane265BtpGenLeaf0000', tree)


if __name__ == '__main__':
    unittest.main()
