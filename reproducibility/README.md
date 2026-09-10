# Reproduction

## Start with the Packaged Inputs

From the repository root, Python 3.10 or later is enough to check the frozen
proof inputs without installing a scientific environment:

~~~sh
make integrity
~~~

This verifies input identities, not the theorem. A Git checkout needs
`git lfs pull` to obtain the actual large files; the release ZIP contains
the payloads directly. Primary replay has been tested on Linux with Python 3.12.

## Choose the Check You Need

| Command | Additional dependencies | What it checks or produces |
| --- | --- | --- |
| `make test` | Python standard library and Poppler (`pdfinfo`) | Regression and release-tool tests |
| `make check` | Poppler (`pdftotext`) | Tests, exact public inventory, hashes, links and report identifiers |
| `make verify` | Verification Python dependencies; `drat-trim` | Reconstructs occupation rows and freshly checks eight proofs |
| `make verify-full` | Above, C++17 compiler and pinned upstream verifier | Also regenerates CNFs, re-expands the full lookup table and replays the upstream certificate |
| `make reports` | XeLaTeX, BibTeX, latexmk, CTeX, Noto CJK and Poppler | English report and its complete Chinese translation, each with integrated appendices |
| `make reports-en` / `make reports-zh` | Corresponding report dependencies | Build one language while preserving the other edition's receipt |
| `make figures` | XeLaTeX, pdfcrop/Ghostscript and Poppler | README images from the report's exact TikZ sources |
| `make source-en` | Report-building dependencies | Self-contained source ZIP, verified by a standalone rebuild |
| `make source-zh` | Chinese report-building dependencies | Self-contained Chinese source ZIP, also checked against its maintained PDF |
| `make package` | Dependencies of `make check` | Hash-checked release ZIP from the reviewed public manifest |

Create a project-specific environment instead of modifying a shared research
installation:

~~~sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-verification.txt
make verify PYTHON=.venv/bin/python
~~~

Build `drat-trim` with `make` in its
[official source repository](https://github.com/marijnheule/drat-trim), then
place the executable on `PATH`. Dependency installation may need network
access; mathematical replay itself needs no language model, network search,
private account or running Qiushi service. The checker verifies the supplied
CNF; the independent semantic checks address what that CNF represents.

On slower machines increase the per-proof limit, for example
`make verify PYTHON=.venv/bin/python DRAT_TIMEOUT=900`.
The default 90 seconds is a timeout, not a promised execution time.

## Complete Primary Replay

The upstream certificate verifier source is
[tensor-rank-lower-bound](https://github.com/wcgbg/tensor-rank-lower-bound)
at commit d96d787bf4845d90b4100e1a94279715a9d54317.
The tested drat-trim executable had SHA-256
b535cc5334e97fba5b5db6013625c5a0b16ce348a98d59ff91b45a83fa56b39e.
These identify tested dependencies, not a claim that every platform has
rebuilt them.

The upstream adapter command used by the full entry is:

~~~text
qiushi-matmul lower-bound verify-wang-q2-333 <certificate>
~~~

The public compatibility adapter is included in tools/qiushi-matmul.
It accepts only the exact pinned certificate and invokes an upstream
verifier executable selected through WANG_VERIFIER. It needs no private
Qiushi installation. In the pinned upstream checkout, its documented command
builds the problem-specific verifier and verifies the certificate:

~~~sh
python3 run.py verify /absolute/path/to/cert_matrix_q02_n333.pb.txt
~~~

That upstream build requires Git LFS, Bazelisk and a C++20 toolchain.
Then, in this research repository:

~~~sh
export WANG_VERIFIER=/absolute/path/to/upstream/bazel-bin/verifier/verifier_main
make verify-full PYTHON=.venv/bin/python
~~~

The adapter was tested against the existing pinned verifier binary.
A clean external-machine rebuild of the C++ dependency has not been
claimed. `verify-full` selects the included compatibility adapter
automatically; the other verification targets do not require it.
Full replay checks the existing proof and does not run new solver searches.

Fresh results go to build/verification/. A failed child process, missing
result, malformed result or old success cannot pass as a new verification.
Timeouts terminate and reap the child process group.

The separate unary proof chain and some algebraic diagnostics are retained
as historical evidence. A primary replay must not be described as fresh
execution of every auxiliary check.

## Trust and Portability

Lookup files use Python pickle for compatibility. Run only reviewed
hash-bound inputs; this verifier is not a sandbox for untrusted programs.
Git LFS pointer files are not proof payloads. Verification is tested on Linux.
Source ZIPs and PDFs can be extracted or read on Windows; that does not
establish native Windows mathematical replay.

TeX fonts are resolved by standard TeX Live filenames. Standalone source
packaging rebuilds the selected language without private file paths and
compares its extracted PDF text with the maintained report. The Chinese
translation uses CTeX and the public Noto CJK fonts
(`texlive-lang-chinese` and `fonts-noto-cjk` on Ubuntu/Debian);
it preserves the English figures, author order, equations and bibliography,
with bilingual author names and typography adapted for Chinese reading.
Each language has one master file, `main.tex`.

The upstream MIT notice is in
[licenses/tensor-rank-lower-bound-MIT.txt](licenses/tensor-rank-lower-bound-MIT.txt).
External tools are not newly relicensed by this project.

## Maintaining a Release

An unchanged reproducible report rebuild preserves its receipt. Changed
sources or artifacts require review and an intentional refresh of
`evidence/release-manifest.json` before packaging. This manifest is an
explicit public-file list, not an instruction to publish everything on disk.

`make package` checks the inventory and source hashes, verifies the ZIP's
contents, and refuses to overwrite an existing archive. It excludes Git
history, local environments and build outputs. The root LICENSE defines
reuse rights. A local build does not submit the report or publish the repository.
