# BTP Trace Semantics

## Reusable Extraction

`PaddedExtraction.lean` proves:

```lean
QiushiMatmul.FrozenRegistry.padded_plane_qra
  (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
  (hZero : forall c : Fin 512, (cfg.classifyCode c).val = 0 ->
    spanContainsCode cfg.planeBasis c.val = true)
  (pad : Fin cfg.nLive)
  (hSource : forall i : Fin cfg.nOcc,
    QuotientRankAtLeast (cfg.sourceU i) (cfg.sourceLb i))
  (hNoModel : forall x : Fin cfg.nLive -> Int,
    cfg.occSys.RootHolds x -> False) :
  QuotientRankAtLeast cfg.W (cfg.target + 1)
```

It reuses `live_labeled_fiber_occ_row_int_padded`. Every hypothetical length
`r <= target` decomposition gives a nonnegative integer vector of total
`target`, after carrying the zero quotient fiber and padding one live label.
The sharp source inequality includes the zero fiber before padding, so no
source capacity is weakened. A source lower bound greater than the target
already excludes the decomposition. The matrix-code classifier, source
containments, section representatives, coefficient indicators, and RHS values
are all connected by the existing `PlaneExtBool` checks.

The theorem needs an explicit live label `pad`; it does not apply to the empty
live-label type. For the full-space representative 0, the registry proves only
the trivial required bound 0. Representative 495 instead quotients by the zero
subspace, using the existing bound 21 to discharge its required bound 20; it is
not an empty-live-label case. The extraction theorem does not assume that the zero fiber vanishes and
requires no quotient-rank theorem for any dead-witness field. The emitted
configuration's single dummy dead table is just the base space and certifies
the label-zero classification; it supplies no rank premise.

## Deterministic Trace Translation

`btp_to_lean.py` consumes the actual archived leaf depths, selected-path masks,
and invertible query/store witnesses. No solver, orbit search, or new trace
search runs. It translates each DFS node into binary integer decisions:

```text
x[label] <= prefix_count[label]
or
x[label] >= prefix_count[label] + 1.
```

The first child tests the next lower label; the second follows the corresponding
recorded DFS child. Repeated path labels remain integer multiplicities. When
all labels are exhausted, their upper bounds contradict the total-count row.
At an archived leaf, its source occupation row, the selected multiplicity lower
bounds, and remaining nonnegativity rows form an exact Farkas contradiction.

The emitted Lean uses the established `farkas_leaf_unsat` and exhaustive
`by_cases` integer splits. Every branch is proved, including exhaustion
branches absent as explicit records in the compressed archive. The translator
is not trusted: malformed arithmetic, incompatible source matrices, missing
branch hypotheses, or unclosed children cannot establish the final Lean theorem.

Actual source declarations and their bounds are supplied explicitly. Recorded
matrices are inverted into the existing checked-transport convention. The
source need only contain the canonical image; no containment is incorrectly
reversed. Both matrix invertibilities, inverse identities, every generator
pair, and bound weakening are checked again in Lean.

Independent `FrozenRegistry` source modules can be reused. The translator
checks their local import closure and rejects the aggregate `Bindings` module,
the node being emitted, and import cycles. Orbit-containment entries use their
already proved `Transport.boundNNN` on the exact frozen basis, rather than
incorrectly identifying that basis with the generally larger raw source.
Source ranks remain theorem arguments checked by Lean, not accepted metadata.

With the optional `--singleton-cover`, the translator still checks the complete
archive trace and extracts its witnessed source spaces. If every live label has
a source occupation row supported on exactly that label, it selects the least
capacity for each label. When their sum is strictly below `target`, adding those
rows to the total-count row gives one exact Farkas contradiction. No solver or
new branch search is run. Missing coverage or insufficient capacity fails this
mode explicitly. This is a compressed proof from the archived sources, not a
claim that the original branch tree is replayed unchanged.

`--root-farkas` allows nonnegative integer weights on the same witnessed
occupation rows, the total-count row, and nonnegativity rows. SciPy/HiGHS
proposes one root dual ray with a 30-second limit and one solver thread;
rationalization is followed by exact integer cancellation and strict-negative
right-hand-side checks. A failed proposal or exact check is rejected. No new
orbit or integer-branch search is performed. The weights are emitted through
the existing Lean Farkas checker; neither the LP result nor the Python checker
is an axiom. This optional generation mode additionally requires NumPy/SciPy.

Both compression modes validate the full archived DFS trace, but avoid
materializing its binary count tree. The output's `translated_leaves: null`
records this distinction; `emitted_leaves` is one. Actual source bases, both
transport invertibilities, source bound strength, and the zero-fiber padding
interface are unchanged.

## Checked Instances

Node 285 proves `QuotientRankAtLeast (spanCodes [96,20,10,1]) 17`.
The complete 17,571-leaf trace supplies 39 witnessed source rows. Root
compression uses 23 occupation rows with weights 1 or 2, plus total and
nonnegativity rows, yielding the exact right-hand side -4 at target 16.
All 54 node modules and the final frozen-type/standard-axiom guards passed.
The source IDs are 16, 20, 23, 35, 97, 117, 126, 156, 162, 163, 164, 165,
and 166. Regenerate with `--node 285 --leaf-limit 18000 --root-farkas
--emit-tests`; the unchanged target does not require a new branch search.

Node 287 proves `QuotientRankAtLeast (spanCodes [160,20,10,1]) 17`.
Its complete 301,845-leaf trace supplies 68 witnessed source rows. One root
ray uses 19 occupation rows, the total-count row, and two nonnegativity rows,
all with weight 1, giving right-hand side -1 at target 16. All 59 node
modules and the final frozen-type/standard-axiom guards passed. The source
IDs are 14, 35, 55, 57, 64, 65, 67, 76, 79, 80, 82, 99, 120, 127, 157,
158, 159, 162, 163, 172, 173, 174, and 175. Regenerate with `--node 287
--leaf-limit 302000 --root-farkas --emit-tests`. The large archived tree
is checked for trace completeness, not expanded into new integer branches.

Node 410 proves `QuotientRankAtLeast (spanCodes [4,2,1]) 15` from the
63 witnessed singleton source rows of its complete 63-leaf archived trace.
The source bounds for 248 and 249 are both 14. All 63 capacities are zero at
the counterexample target 14, so their sum and the total-count row give one
Farkas leaf with right-hand side -14. All 57 node modules and the exact
frozen-type/standard-axiom guards passed. Regenerate with `--node 410
--singleton-cover --emit-tests`; no new branch search is involved.

Node 420 proves `QuotientRankAtLeast (spanCodes [68,10,1]) 18`. Its complete
67-leaf archived trace supplies 63 singleton rows with total capacity 3 at
the counterexample target 17. One Farkas leaf has right-hand side -14.
Sources are 253, 279, 284, 290, 300, 301, and 302. All 57 node modules and
the exact frozen-type/standard-axiom guards passed. Regenerate with
`--node 420 --singleton-cover --emit-tests`.

The node-227 package translates 277 original leaves into 520 integer-system
leaves, batched into 33 compilation modules. Its 15 source rows use only
representatives 47, 48, 57, 60, 61, 68, 78, 83 through their established source
declarations. The exact target is:

```lean
QuotientRankAtLeast (spanCodes [294,140,96,16,1]) 15
```

All 85 modules in the focused source closure compiled, including the two
frozen-table prerequisites, reusable extraction, and final tests.
`Btp227Tests.lean` checks its actual frozen-table type and guards the transitive
axioms of the final bound, no-model theorem, source dispatch, and padded
extraction; all four guards pass with only `propext`, `Classical.choice`, and
`Quot.sound`. A successful focused build is the acceptance condition, not
translation success or an original protobuf rank label.

The second checked instance is node 224:

```lean
QuotientRankAtLeast (spanCodes [302,132,96,16,1]) 15
```

Its 421 archived leaves translate into 664 integer-system leaves. The 15
source rows reuse only representatives 47, 60, 66, 68, and 79. All 91 node
modules, including `Btp224Tests.lean`, compiled; its final bound, no-model
theorem, and source dispatch have only the same three standard axioms.

Node 260 proves `QuotientRankAtLeast (spanCodes [80,12,2,1]) 16`.
Its 87 archived leaves translate into 128 checked leaves on 33 source rows.
All 61 node modules and final type/axiom guards passed. Its sources are
20, 88, 97, 98, 101, 117, 122, 123, and 124; source 122 uses the independently
checked exact frozen-basis orbit adapter. It requires the completed 88 and 20
source packages in addition to the original clean import closure.

Node 265 proves `QuotientRankAtLeast (spanCodes [272,12,2,1]) 16`.
Its 219 archived leaves translate into 475 checked leaves on 31 source rows.
All 81 node modules and final type/axiom guards passed. Its sources are
90, 100, 105, 107, 110, 113, 120, 121, 124, 125, 127, 128, 129, 130, and 132;
source 90 uses the independently checked exact frozen-basis orbit adapter.

Node 261 uses this compression to prove
`QuotientRankAtLeast (spanCodes [96,12,2,1]) 16`. The full 1,169-leaf trace is
validated; its 34 witnessed source rows include 31 singleton rows whose total
capacity is 10, contradicting the required total 15. The single emitted Farkas
leaf has RHS -5. All 54 node modules and final type/axiom guards passed, with
only the three standard axioms. Sources are 20, 23, 88, 99, 106, 112, 117,
125, 126, 127, and 128.

Node 263 similarly proves `QuotientRankAtLeast (spanCodes [160,12,2,1]) 16`.
Its validated 521-leaf trace yields 31 singleton source rows with total
capacity 9, so the single emitted leaf has RHS -6. All 52 node modules and
final type/axiom guards passed. Sources are 90, 97, 99, 107, 111, 112, 118,
123, 125, 130, 131, and 132. Neither compact proof weakens the frozen target.

Regenerate these two instances with `--singleton-cover --emit-tests`, choosing
node 261 or 263 and adding `--leaf-limit 2000` for 261. The proof modules remain
checkable without executing the translator or reading the binary archive.

## Replay

The committed Lean package can be built directly, without the binary archive:

```sh
python3 tools/frozen_registry.py build-missing FrozenRegistry.Btp227Tests \
  --environment "$CLEAN_ENVIRONMENT_JSON" --output "$PRIVATE_BUILD_OUTPUT"
```

To regenerate, hydrate the pinned public BTP object and use the certificate
emitter version supporting `module_prefix` and supplied `transports`:

```sh
python3 FrozenRegistry/btp_to_lean.py \
  --archive "$BTP_ARCHIVE" \
  --certificate ../proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt \
  --registry FrozenRegistry/checked.json --node 227 \
  --output "$PRIVATE_GENERATION_OUTPUT" \
  --emitter tools/generate_certificate.py --emit-dir "$PRIVATE_SOURCE_OUTPUT" \
  --emit-tests
BTP_ARCHIVE="$BTP_ARCHIVE" CERTIFICATE_EMITTER=tools/generate_certificate.py \
  python3 FrozenRegistry/test_btp_to_lean.py
```

The twelve translator tests check source closure, all translated paths and leaf
hypotheses, malformed/incomplete trace rejection, absent or insufficient source
bounds, cyclic aggregate-source rejection, independent orbit/BTP source reuse,
emitted guards, singleton-cover and exact root-ray compression and their rejection cases, staged
leaf cleanup, and repeated byte-identical source regeneration. `--emit-tests`
adds an exact frozen-type example and transitive axiom guards for each instance.
The default decode limit is 1,000 archived leaves; larger instances require an
explicit `--leaf-limit`. Increasing this bound does not solve proof-size growth.
This route does not prove correctness of a general binary parser,
the entire original C++ verifier, or every archive entry at once. Each accepted
instance is a kernel-checked rank proof from explicitly checked source bounds.
