#!/usr/bin/env python3
"""Inspect public files and source archives without executing research code."""
import argparse
import ast
import io
import json
import math
from pathlib import Path
import re
import struct
import subprocess
import zipfile
import zlib
import warnings

from check_release import public_files

ROOT = Path(__file__).resolve().parents[1]
RULES = {
    'private-host-path': re.compile('/' + r'(?:data/qiushi|home/(?:ubuntu|kemove)|root/\.ssh)(?:/|\b)', re.I),
    'execution-identifier': re.compile(r'S' + r'09\d{2}A0[12]', re.I),
    'numbered-execution-record': re.compile(r'\b' + r'Steps?[ _-]*\d+\b', re.I),
    'private-key': re.compile('-----BEGIN ' + r'[A-Z ]*PRIVATE KEY-----'),
    'credential-token': re.compile(r'\b(?:sk|ghp|github_pat)[_-][A-Za-z0-9_-]{24,}'),
    'editorial-confirmation': re.compile('(?:author order|authors?) (?:was |were )?' + r'confirmed by|project owner on \d', re.I),
}
TEXT = {'.md', '.txt', '.py', '.cpp', '.c', '.h', '.hpp', '.json', '.jsonl',
        '.csv', '.qmm', '.tex', '.bib', '.bbl', '.bst', '.cff', '.sh', '.sage',
        '.wl', '.sing', '.dimacs', '.set'}


def matches(text):
    return [name for name, pattern in RULES.items() if pattern.search(text)]


def png_metadata(data):
    if not data.startswith(b'\x89PNG\r\n\x1a\n'):
        raise ValueError('invalid PNG signature')
    offset, texts = 8, []
    while offset + 12 <= len(data):
        size = struct.unpack('>I', data[offset:offset + 4])[0]
        kind = data[offset + 4:offset + 8]
        payload = data[offset + 8:offset + 8 + size]
        if len(payload) != size:
            raise ValueError('truncated PNG chunk')
        if kind == b'tEXt':
            texts.append(payload.decode('latin1'))
        elif kind == b'zTXt':
            key, rest = payload.split(b'\0', 1)
            if not rest or rest[0] != 0:
                raise ValueError('unsupported PNG text compression')
            texts.append(key.decode('latin1') + zlib.decompress(rest[1:]).decode('latin1'))
        elif kind == b'iTXt':
            key, rest = payload.split(b'\0', 1)
            flag, method, rest = rest[0], rest[1], rest[2:]
            language, translated, text = rest.split(b'\0', 2)
            if flag:
                if method != 0:
                    raise ValueError('unsupported PNG text compression')
                text = zlib.decompress(text)
            texts.append((key + b' ' + translated + b' ' + text).decode('utf-8'))
        elif kind == b'eXIf':
            texts.append(payload.decode('latin1'))
        offset += size + 12
        if kind == b'IEND':
            return texts
    raise ValueError('PNG has no complete end chunk')


def numpy_header(data):
    if data[:6] != b'\x93NUMPY' or len(data) < 10:
        raise ValueError('invalid NumPy header')
    major = data[6]
    if major == 1:
        start, size = 10, struct.unpack('<H', data[8:10])[0]
    elif major in (2, 3):
        start, size = 12, struct.unpack('<I', data[8:12])[0]
    else:
        raise ValueError('unsupported NumPy format')
    header = ast.literal_eval(data[start:start + size].decode('utf-8' if major == 3 else 'latin1'))
    dtype = header['descr']
    if not isinstance(dtype, str) or not re.fullmatch(r'[<>=|][buifc]\d+', dtype):
        raise ValueError('array is not a plain numeric dtype')
    dimensions = header['shape']
    if not isinstance(dimensions, tuple) or not all(type(n) is int and n >= 0 for n in dimensions):
        raise ValueError('invalid numeric array shape')
    if len(data) != start + size + math.prod(dimensions) * int(dtype[2:]):
        raise ValueError('numeric array payload length does not match its shape')
    return header


def inspect_bytes(name, data):
    errors = matches(name)
    suffix = Path(name).suffix.lower()
    if suffix in TEXT or Path(name).name in {'LICENSE', 'Makefile'}:
        text = data.decode('utf-8')
        errors.extend(matches(text))
        if suffix == '.json':
            json.loads(text)
        if suffix == '.py':
            with warnings.catch_warnings():
                warnings.simplefilter('ignore', SyntaxWarning)
                ast.parse(text, filename=name)
    elif suffix == '.png':
        for text in png_metadata(data):
            errors.extend(matches(text))
    elif suffix == '.npy':
        numpy_header(data)
    elif suffix == '.npz':
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            if sum(i.file_size for i in archive.infolist()) > 512 << 20:
                raise ValueError('numeric archive exceeds inspection limit')
            for member in archive.infolist():
                if not member.filename.endswith('.npy'):
                    raise ValueError('unexpected numeric archive member')
                errors.extend(matches(member.filename))
                numpy_header(archive.read(member))
    elif suffix in {'.pkl', '.btp', '.cnf', '.drat'}:
        # Inspect embedded labels without deserializing or executing the payload.
        errors.extend(matches(data.decode('latin1')))
    return sorted(set(errors))


def audit(root, archive_path=None):
    failures, count, pdfs = [], 0, []
    if archive_path:
        with zipfile.ZipFile(archive_path) as archive:
            if archive.testzip() is not None:
                raise ValueError('archive CRC failure')
            for member in archive.infolist():
                if member.is_dir():
                    continue
                if Path(member.filename).is_absolute() or '..' in Path(member.filename).parts:
                    raise ValueError('unsafe archive path')
                try:
                    errors = inspect_bytes(member.filename, archive.read(member))
                except (ValueError, SyntaxError, UnicodeError, KeyError, struct.error) as e:
                    errors = [type(e).__name__]
                failures.extend({'path': member.filename, 'rule': error} for error in errors)
                count += 1
    else:
        for name in sorted(public_files(root)):
            path = root / name
            if path.is_symlink():
                failures.append({'path': name, 'rule': 'symlink'})
                continue
            try:
                errors = inspect_bytes(name, path.read_bytes())
                if path.suffix.lower() == '.pdf':
                    texts = [subprocess.check_output(['pdftotext', '-layout', str(path), '-'], text=True),
                             subprocess.check_output(['pdfinfo', str(path)], text=True)]
                    for text in texts:
                        errors.extend(matches(text))
                    pdfs.append(name)
            except (ValueError, SyntaxError, UnicodeError, KeyError, struct.error) as e:
                errors = [type(e).__name__]
            failures.extend({'path': name, 'rule': error} for error in sorted(set(errors)))
            count += 1
    return {'schema': 'qiushi.matmul.public-privacy-check.v1', 'all_ok': not failures,
            'files_checked': count, 'pdf_text_and_metadata_checked': pdfs,
            'rules': list(RULES), 'failures': failures,
            'scope': 'Known private identifiers and credential patterns, text formats, numeric array headers, binary proof/cache labels, PNG metadata, and rendered PDF text/metadata. Not an absolute guarantee of absence of every possible sensitive fact.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--archive', type=Path)
    args = parser.parse_args()
    result = audit(args.root.resolve(), args.archive)
    print(json.dumps(result, indent=2))
    return 0 if result['all_ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
