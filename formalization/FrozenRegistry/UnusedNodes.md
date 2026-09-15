# Frozen-Node Certificate Reuse

The complete 496-entry registry has no remaining representative-rank goals.
`All.lean` and `Global.lean` give unconditional representative and frozen-L0
rank soundness; all exact-type and standard-axiom guards passed. Entry 260
retains its compact seven-space source, with BTP260 as a checked alternative.
`Remaining.lean` proves that the complement is empty. The dependency inventories
below describe earlier discovery checkpoints, not current theorem assumptions.
`Reductions.lean`
checks the conditional implications 162 -> 341, 284 -> 418, 289 -> 441,
including exact invertible GL/transpose transport for 341.

## The Existing Archive Contains Traces

The public `cert_matrix_q02_n333.btp` is a Git LFS object: 33,013,656 bytes,
SHA-256 `4e824eb13c235e69045881d173d8ababe622421055a238005afce413aabe3289`.
Its `BTPARCH` version-2 header has 496 slots and 238 nonempty traces. Each
nonempty slot is a gzip stream with a 64-bit leaf count, followed by four
parallel arrays: 8-bit DFS depth, 32-bit mask, query element, and store element.
The lengths match all protobuf backtracking sizes. At the 409 checkpoint,
all 84 remaining backtracking entries had traces, totalling 22,227,970 leaves.
The subsequent four backtracking bindings and one degeneration binding reduce
the remaining set to 80 traces plus two degeneration consequences. The checked
227 replay removes a further 277 leaves, leaving 79 traces with 22,227,439 leaves
and the two degeneration consequences at the 415 checkpoint.

The earlier metadata inspection covered only the protobuf, not this archive.
It must not be read as evidence that branch traces are unavailable.
The public upstream reader and verifier are pinned by `reproducibility/README.md`:
`core/backtracking_proof.cc`, `verifier/backtracking_verifier.h`, and
`problems/matrix/symmetry.h` at commit
`d96d787bf4845d90b4100e1a94279715a9d54317`.

The verifier reconstructs deterministic DFS paths with repetitions, consumes
one record per leaf, and checks the masked extension's exact witness into a
larger frozen source. Its numeric check is
`popcount(mask) + source_lower >= target_lower`. A future Lean adapter must
retain complete child coverage, repeated summand multiplicities, the zero
fiber/decomposition-length condition, both matrix invertibilities, actual
source bases, and established source ranks. Numeric labels are not rank proofs.

## Short Recorded Dependencies

Finite DFS structure and exact binary witness arithmetic identify:

| Node | Leaves | Actual source IDs | Still-unregistered sources at 409 |
| --- | ---: | --- | --- |
| 24 | 127 | 5, 7, 9 | none |
| 27 | 127 | 7, 8, 9 | none |
| 28 | 127 | 9 | none |
| 33 | 127 | 5, 11, 13 | none |
| 88 | 31 | 5, 19, 20, 23, 24, 25 | 24 |
| 273 | 31 | 91, 97, 101, 134 | none |
| 284 | 41 | 96, 106, 150, 156, 159, 160, 161 | none |
| 410 | 63 | 248, 249 | 248, 249 |
| 420 | 67 | 253, 279, 284, 290, 300, 301, 302 | 284, 301, 302 |

At the 409 checkpoint, node 289 had 45,053 leaves and 29 source IDs;
only source 33 was then unregistered.
These are decoded dependency interfaces, not new kernel-checked rank bindings.
The original 181 trace also uses 33; the independently regenerated certificate
avoids that dependency, so the registry uses the completed proof unchanged.

Do not redo orbit discovery or a large branch search before exploiting these
existing witnesses. The existing `generic_plane_qra` and Farkas emitter remain
available for smaller occupation certificates; they need proved source bounds,
a positive dead-witness count, and a proved integer-system contradiction.
The per-instance replay route is now implemented in `btp_to_lean.py` and
`PaddedExtraction.lean`. It checks an exhaustive integer-tree translation with
the existing Farkas semantics. The node-227 instance passes kernel compilation
and exact-type/axiom guards; see `BtpSemantics.md`. This does not claim a general
verified binary decoder or a simultaneous proof of all archived nodes.

## Bounded Reader

`btp_archive.py` verifies the pinned archive/protobuf hashes, all slot lengths,
and selected complete DFS traces. Per trace it checks every child, mask, actual
matrix witness, larger-dimensional canonical source, and required numeric bound.
Its output names required rank interfaces and whether they are registered; it
does not certify those ranks. The default explicit decode limit is 100,000
leaves per selected node. Larger traces are reported as not decoded, not passed.

For each distinct recorded witness it also exports `P`, `Q`, `Qinv`, `flip`,
and generator pairs in the existing `generate_certificate.py` transport format.
The archive action is `canonical = L * transpose^flip(actual) * R^-1`;
the exported inverse action is
`actual = P^T * transpose^flip(canonical) * Qinv^T`. Matrix inverses and both
directions are checked in the reader tests. These exported numbers still need
the existing Lean transport proof and actual source theorem before rank reuse.

From `formalization`, with the public Git LFS object hydrated:

```sh
python3 FrozenRegistry/btp_archive.py \
  --archive "$BTP_ARCHIVE" \
  --certificate ../proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt \
  --registry FrozenRegistry/checked.json \
  --node 33 --node 162 --node 410 --output "$PRIVATE_TRACE_REPORT"
BTP_ARCHIVE="$BTP_ARCHIVE" python3 FrozenRegistry/test_btp_archive.py
```

The nine tests include pinned input checks and negative tests for truncation,
wrong headers, invalid masks, missing/extra leaves, singular witnesses, weak
source labels, and incomplete child coverage. No solver or fresh orbit search
is needed. The `BTP_ARCHIVE` environment variable only enables the optional
corpus test; ordinary codec tests use synthetic fixtures.

The further recorded dependency chain at 414 is:
`410 <- {248,249}`, `248 <- {27,87,88}`, `249 <- {88,92}`, `92 <- {27,28}`,
listing only unregistered prerequisite IDs. Nodes 87, 109, 162, 224, 227, 240,
301, and 302 have only registered rank prerequisites in their decoded traces.
Their original traces have respectively 1303, 14340, 10368, 421, 277, 2047,
10254, and 635 leaves. These findings narrow reuse work; none adds a registry
binding without a kernel proof.
