import io
import pickle
from pathlib import Path
import struct
import sys
import tempfile
import unittest
import zipfile
import zlib

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import audit_public


def chunk(kind, payload):
    return struct.pack('>I', len(payload)) + kind + payload + struct.pack('>I', zlib.crc32(kind + payload))


class PublicAuditTests(unittest.TestCase):
    def test_identifier_in_text_is_rejected(self):
        sample = ('S' + '0904' + 'A01').encode()
        self.assertIn('execution-identifier', audit_public.inspect_bytes('note.md', sample))

    def test_lean_sources_and_dependency_records_are_inspected(self):
        sample = ('S' + '0904' + 'A01').encode()
        for suffix in ('.lean', '.toml', '.log', '.inc'):
            with self.subTest(suffix=suffix):
                self.assertIn('execution-identifier',
                              audit_public.inspect_bytes('source' + suffix, sample))

    def test_local_lean_proof_names_are_not_execution_records(self):
        self.assertEqual(audit_public.inspect_bytes('Proof.lean', b'have step' + b'1 : True := True.intro'), [])
        self.assertIn('numbered-execution-record',
                      audit_public.inspect_bytes('Proof.lean', b'-- imported from Step' + b' 75'))

    def test_compressed_png_metadata_is_checked(self):
        sample = ('S' + '0904' + 'A01').encode()
        data = b'\x89PNG\r\n\x1a\n' + chunk(b'zTXt', b'Comment\0\0' + zlib.compress(sample)) + chunk(b'IEND', b'')
        self.assertIn('execution-identifier', audit_public.inspect_bytes('figure.png', data))

    def test_formal_author_contact_is_not_redacted(self):
        self.assertEqual(audit_public.inspect_bytes('authors.tex', b'Rui Zhao; Junyao Wu; yangyihao@zju.edu.cn'), [])

    def test_private_label_inside_binary_cache_is_rejected(self):
        data = pickle.dumps({'lut': {1: 19}, 'meta': {'cert': 'S' + '0904' + 'A01/cert.txt'}})
        self.assertIn('execution-identifier', audit_public.inspect_bytes('cache.pkl', data))

    def test_binary_cache_with_public_label_is_accepted(self):
        data = pickle.dumps({'lut': {1: 19}, 'meta': {'cert': 'assets/cert.txt'}})
        self.assertEqual(audit_public.inspect_bytes('cache.pkl', data), [])

    def test_editorial_confirmation_is_rejected(self):
        text = ('The author order was ' + 'confirmed by the project owner.').encode()
        self.assertIn('editorial-confirmation', audit_public.inspect_bytes('README.md', text))

    def test_source_archive_members_are_checked(self):
        with tempfile.TemporaryDirectory() as td:
            archive = Path(td) / 'source.zip'
            with zipfile.ZipFile(archive, 'w') as stream:
                stream.writestr('main.tex', 'S' + '0904' + 'A01')
            result = audit_public.audit(Path(td), archive)
            self.assertFalse(result['all_ok'])

    def test_object_array_is_rejected_without_loading_pickle(self):
        header = b"{'descr': '|O8', 'fortran_order': False, 'shape': (1,)}\n"
        data = b'\x93NUMPY\x01\x00' + struct.pack('<H', len(header)) + header
        with self.assertRaises(ValueError):
            audit_public.inspect_bytes('array.npy', data)

    def test_plain_numeric_array_is_accepted(self):
        header = b"{'descr': '|u1', 'fortran_order': False, 'shape': (1,)}\n"
        data = b'\x93NUMPY\x01\x00' + struct.pack('<H', len(header)) + header + b'\x00'
        self.assertEqual(audit_public.inspect_bytes('array.npy', data), [])

    def test_malformed_result_is_not_validated(self):
        with self.assertRaises(ValueError):
            audit_public.inspect_bytes('result.json', b'{"all_ok":')


if __name__ == '__main__':
    unittest.main()
