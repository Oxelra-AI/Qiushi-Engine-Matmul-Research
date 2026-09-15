"""Read original proof-node metadata; this does not verify proof payloads."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from google.protobuf import descriptor_pb2, descriptor_pool, message_factory, text_format

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from generate_frozen_table import read_representatives


def read_metadata(path):
    schema = descriptor_pb2.FileDescriptorProto(name='registry_metadata.proto', syntax='proto3')

    def message(name, fields):
        msg = schema.message_type.add(name=name)
        for number, fname, kind, typ, repeated in fields:
            field = msg.field.add(name=fname, number=number, type=kind,
                                 label=3 if repeated else 1)
            if typ:
                field.type_name = '.' + typ
        return msg

    message('FlattenMatrixProof', [])
    message('ForcedProductProof', [(1, 'projection_type', 13, None, False)])
    message('Transformation', [(1, 'query_elem', 7, None, False),
                               (2, 'store_elem', 7, None, False)])
    message('DegenerateProof', [(1, 'extra_constraint', 7, None, False),
                                (2, 'transformation', 11, 'Transformation', False)])
    message('BacktrackingProof', [(1, 'proof_size', 13, None, False)])
    proof = message('RankLowerBoundProof', [
        (1, 'flatten_matrix_proof', 11, 'FlattenMatrixProof', False),
        (2, 'forced_product_proof', 11, 'ForcedProductProof', False),
        (3, 'degenerate_proof', 11, 'DegenerateProof', False),
        (4, 'backtracking_proof', 11, 'BacktrackingProof', False)])
    proof.oneof_decl.add(name='proof')
    for field in proof.field:
        field.oneof_index = 0
    message('ConstrainedTensor', [
        (1, 'index', 13, None, False), (2, 'constraints', 12, None, False),
        (3, 'constraints_text', 9, None, False), (4, 'tensor_text', 9, None, False),
        (5, 'rank_lower_bound', 5, None, False),
        (6, 'rank_lower_bound_proof', 11, 'RankLowerBoundProof', False),
        (7, 'rank_upper_bound', 5, None, False), (8, 'rank_upper_bound_proof', 9, None, False)])
    message('Certificate', [
        (1, 'problem_name', 9, None, False), (2, 'characteristic', 5, None, False),
        (3, 'extension_degree', 5, None, False), (4, 'na', 5, None, False),
        (5, 'nb', 5, None, False), (6, 'nc', 5, None, False),
        (7, 'constrained_tensors', 11, 'ConstrainedTensor', True)])
    pool = descriptor_pool.DescriptorPool()
    pool.Add(schema)
    cert = message_factory.GetMessageClass(pool.FindMessageTypeByName('Certificate'))()
    text_format.Parse(path.read_text(), cert)
    rows, digest = read_representatives(path)
    for item in cert.constrained_tensors:
        row = rows[item.index]
        proof = item.rank_lower_bound_proof
        kind = proof.WhichOneof('proof')
        row['proof_type'] = kind
        if kind == 'backtracking_proof':
            row['proof_size'] = proof.backtracking_proof.proof_size
        elif kind == 'degenerate_proof':
            p = proof.degenerate_proof
            row.update(extra_constraint=p.extra_constraint,
                       query_elem=p.transformation.query_elem,
                       store_elem=p.transformation.store_elem)
        elif kind == 'forced_product_proof':
            row['projection_type'] = proof.forced_product_proof.projection_type
    return dict(certificate_sha256=digest, rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--remaining', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = read_metadata(args.certificate)
    remaining = json.loads(args.remaining.read_text())
    selected = [data['rows'][r['index']] for r in remaining]
    for requested, actual in zip(remaining, selected):
        if any(requested[k] != actual[k] for k in ('index', 'basis', 'lb')):
            raise ValueError('Remaining goal does not match original certificate')
    data['rows'] = selected
    data['proof_types'] = dict(Counter(r['proof_type'] for r in selected))
    args.output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data['proof_types']))
    for row in selected:
        print(json.dumps(row))
