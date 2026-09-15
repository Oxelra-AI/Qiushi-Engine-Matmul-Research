# Lean Formalization

This project formalizes the structural proof of
`R_F2(T_333) >= 21`, including the finite quotient bounds used by the proof.
The toolchain is Lean 4.33.1 with the Mathlib revision fixed in
`lake-manifest.json`. It does not require a running Qiushi Engine.

[Formalization companion (PDF)](report.pdf) explains the theorem, proof
structure, finite certificates and reuse interfaces in three pages.
Its [LaTeX source](report.tex) builds with
`latexmk -pdf -outdir=.local/report-build report.tex`.
The full mathematical argument and research trajectory are presented in the
[English](../reports/en-lean/main.pdf) and [Chinese](../reports/zh-lean/main.pdf)
Lean-integrated reports; the original report editions remain unchanged.

## Proof Status

The main theorem is **closed without finite-bound hypotheses**.
`QiushiFinalTheorem.lean` proves `rank_ge_21`, the interval
`rank_between_21_and_23`, and `bilinear_mul_requires_21` for ordinary
matrix multiplication on all inputs over `ZMod 2`.

The complete 8,455-module local source closure passed a clean build.
`tests/Statements.lean` checked the public interfaces and their transitive
axioms: only `propext`, `Classical.choice` and `Quot.sound` occur.
All 496 frozen representative bounds, their unconditional global rank-soundness
theorem, and the complete calibration statements have passed their source and
axiom checks. Fresh kernel replay has also passed for quotient/restriction
equivalence, general saturation, three-parameter symmetry, affine geometry,
subspace counts and the rank-23 construction. All 13,438 registered modules
now have successful fresh-source build outputs matching the current sources,
including calibration and both report entries. All six independent replay
groups have now passed: 89 terminal declarations and their complete proof
dependencies were checked from an empty kernel environment. This includes the
unconditional main theorem, all finite bounds and complete calibration.
See [STATUS.md](STATUS.md) for verification results
and [COVERAGE.md](COVERAGE.md) for exact statement scopes.

| Component | Entry point |
| --- | --- |
| Tensor, quotient and ordinary multiplication semantics | `QiushiDefs.lean`, `QiushiBilinearSemantics.lean` |
| Three-parameter tensor symmetry and coefficient pullback | `QiushiFullTrilinearSymmetry.lean` |
| Structural lower-bound argument | `QiushiRank21Root.lean`, `QiushiCompositionCheck.lean` |
| Checked actual-subspace transports | `QiushiCertifiedTransport.lean` |
| Rank-one line bound and extension planes | `QiushiLineCoverageFinal.lean` |
| Eight high-pair quotient lower bounds | `QiushiPlane484GenFinal.lean` through `QiushiPlane491GenFinal.lean` |
| All finite premises and unconditional main theorem | `QiushiFinalTheorem.lean` |
| Concrete rank-23 algorithm | `QiushiRank23BilinearSemantics.lean` |
| E11 lifting, occupation caps and saturation consequences | `QiushiTailCoverageChecks.lean`, `QiushiTailPaddedChecks.lean` |
| Main result and complete finite lower bounds | `QiushiReport.lean` |
| Report geometry, calibration and encoding results | `QiushiReportSupplement.lean` |
| Full frozen-table occupation systems | `QiushiFullOccupation.lean` |
| Actual subspace and all-high plane counts | `QiushiMat3SubspaceCount.lean`, `QiushiAllHighPlaneCount.lean` |
| Fourteen two-plane orbits and exact sizes | `QiushiPlaneOrbitFrozenClassification.lean` |
| Exact frozen line and normalized-coset values | `QiushiFrozenL0Exact.lean`, `QiushiFrozenL0LinesAffine.lean` |
| All-dimensional coverage and consistent frozen labels | `QiushiGlobalOrbitCoverage.lean`, `QiushiFrozenLabelConsistency.lean` |
| Complete frozen representative bounds and global L0 rank soundness | `FrozenRegistry/Global.lean`, [interfaces and checks](FrozenRegistry/README.md) |
| Complete calibration geometry, occupation controls and exact capacities | `QiushiCalibrationClosed.lean`, [precise scope](CALIBRATION_SCOPE.md) |
| Boolean copies and disjoint counter encodings | `QiushiOccupationCNF.lean` |

## Build

The build scripts require Python 3.11 or later and a POSIX environment.
Install Elan, then run from this directory:

```sh
lake exe cache get
python3 tools/build.py . --root QiushiMatmul --jobs 4
```

`tools/build.py` schedules local modules by their imports and bounds the number
of active module targets. `--batch-size` combines independent ready targets
in one Lake invocation. Unknown roots, failed builds and blocked
dependencies cause a nonzero exit. Detailed logs are written to `.local/`.
Each compiler process uses one Lean worker; `--jobs` controls process
parallelism. The supplied build and audit scripts also raise their own soft
process-stack limit to 256 MiB when the existing hard limit permits, while
preserving larger or unlimited settings. Lake and direct Lean reserve a
256 MiB worker stack. These settings do not change the kernel or axiom policy.
The explicit root selects the main theorem and its complete dependency closure.
The report's lower-bound and supplementary roots are built separately to keep
import memory bounded. To build every registered module, including both roots
and all existing checks, use:

```sh
python3 tools/build.py . --all --jobs 4
```

To rebuild local sources without reusing this project's compiled artifacts:

```sh
python3 tools/build.py . --all --jobs 4 --fresh-lean
```

This mode copies the selected source closure to a new `.local/build-*/src`
snapshot, resolves the pinned compiler through Lake once, and invokes Lean
directly in dependency order. It writes to an isolated `lib` directory and
excludes the old project build from the import path. Pinned third-party
libraries are still reused. This source build is separate from the subsequent
fresh kernel replay of proof dependencies.

## Finite Certificates

The numbered directories in `certificates/` contain numeric tables,
source-theorem descriptions and exact branch certificates. The Lean proofs
connect these objects through:

1. explicit invertible changes of basis, optionally with transposition;
2. quotient and occupation semantics;
3. exact nonnegative linear combinations of inequalities at each leaf;
4. an exhaustive integer branch split;
5. the resulting quotient-rank lower bound.

The generator is not trusted: its output must compile as Lean proofs. Table
consistency, transports and each contradiction are checked by Lean, rather
than accepted from a saved solver status.

Generators and their regression checks use NumPy, SciPy and Protobuf. The tested
versions are pinned in `requirements-tools.txt`; install these in a separate
Python environment. They are not needed by the Lean kernel:

```sh
python3 -m pip install -r requirements-tools.txt
python3 -m unittest discover -s tests -v
python3 tools/generate_certificate.py \
  --metadata certificates/282/tables.json \
  --certificate certificates/282/branch.json \
  --ledger certificates/282/sources.json \
  --out-dir .local/regenerated-282
```

The default command regenerates transports, branch proofs and the final
instantiation against the checked-in data module. `--data` also emits a
bounded-depth table representation and its semantic checks; changes to that
representation require rebuilding all dependent proofs.

The exhaustive all-high plane count also has a small, deterministic generator:

```sh
python3 tools/generate_all_high_count.py --output .local/regenerated-all-high
```

Its 34 generated Lean files reproduce the checked-in fixtures and row proofs.
The semantic code-to-matrix and six-bases-per-plane arguments are in
`QiushiAllHighCountBridge.lean` and `QiushiAllHighCountSemantics.lean`.
The generator is not a proof oracle: Lean checks every rank lookup and pair
count before deriving the count of actual subspaces.

The intended axiom boundary is `propext`, `Classical.choice` and `Quot.sound`.
No result may be marked complete based only on filenames, generated source,
an external certificate check, or the absence of placeholder text.

After a normal Lake build, audit the compiled statement, its transitive axioms
and its dependency closure with the matching Lean distribution:

```sh
lake env python3 tools/audit.py --project . \
  --toolchain "$(lean --print-prefix)" \
  --module QiushiMatmul --root QiushiMatmul.rank_ge_21 \
  --root QiushiMatmul.bilinear_mul_requires_21 --timeout 43200
```

For an isolated `--fresh-lean` build, select the import path recorded in that
build's `environment.json`; Lake's default project library is not its output.
After the complete report build, the following command checks the main result
and all representative bounds together, replaying their shared dependencies
once. Set `BUILD_DIR` to the directory printed by the completed build:

```sh
BUILD_DIR=.local/build-YYYYMMDD-HHMMSS
PROOF_PATH=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_path"])' \
  "$BUILD_DIR/environment.json")
python3 tools/audit.py --project . --toolchain "$(lake env lean --print-prefix)" \
  --lean-path "$PROOF_PATH" --module QiushiReport --replay-scope roots \
  --root QiushiMatmul.rank_ge_21 \
  --root QiushiMatmul.rank_between_21_and_23 \
  --root QiushiMatmul.bilinear_mul_requires_21 \
  --root QiushiMatmul.FrozenRegistry.all_representatives \
  --root QiushiMatmul.FrozenRegistry.L0_rank_sound \
  --root QiushiMatmul.FrozenRegistry.coverage_with_rank_bound --timeout 43200
```

The supplementary geometry, calibration and encoding results have separate
roots listed in `COVERAGE.md`; the combined command is not their acceptance.

For all report-level groups, use the same fresh build environment:

```sh
python3 tools/verify_all.py --environment "$BUILD_DIR/environment.json" \
  --jobs 2 --timeout 43200
```

`verification.json` selects 89 terminal declarations in six groups: the main
result and global bounds, calibration, classification, full occupation systems,
structural results and consequences, and Boolean encodings. Each group uses the
existing root replayer and its complete dependency closure. Grouping avoids
loading both large report entry points into one process. `--jobs` bounds the
number of simultaneous replays; use one on memory-constrained machines.
`--group encoding` checks only that group and is not report-wide acceptance.
The command does not rebuild sources or replace the source build above.
The large main and calibration groups exceeded two-hour replay budgets on the
validation host. The commands above allow twelve hours per subprocess; this
is a timeout ceiling, not an expected duration. Finite computational proofs
are reduced again by the kernel, so full replay can take substantially longer
than checking a small structural lemma.

The default mode invokes `leanchecker --fresh`. A timeout or a concurrent
artifact change is a failed audit, not a successful verification. Named
definitions and the reported statement must also be compared with the
mathematical claim.

For a narrower declaration-level audit, add `--replay-scope roots`. This
replays every selected declaration and its complete dependency closure from
an empty environment using the pinned distribution's `Lean.Environment.replay`.
It rejects unsafe/partial dependencies and additional axioms; it does not
assume imported proof bodies are valid. The audit records the scope, checks
the exact root types and axioms, and fails on timeout or artifact changes.
Unlike the default whole-module mode, this does not replay unrelated library
declarations. Report-level coverage is provided by all six groups together,
with the precise mathematical statements listed in `COVERAGE.md`.

The replay-driver regression tests include deliberately invalid proof terms,
extra and transitive extra axioms, missing dependencies, unsafe/partial
definitions, and a forged recursor. These test the checking path, not the
matrix-multiplication theorem itself.

Additional translator and build-driver tests live in `FrozenRegistry/` and
`tools/`. Materialize the original BTP archive through Git LFS before running
the archive-dependent checks:

```sh
export BTP_ARCHIVE=../proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.btp
export CERTIFICATE_EMITTER=tools/generate_certificate.py
python3 -m unittest discover -s FrozenRegistry -p 'test_*.py' -v
python3 -m unittest discover -s tools -p 'test_*.py' -v
```
