# Qiushi Engine: Matrix Multiplication Research

<img src="reports/en/figures/qiushi-engine-logo.png" alt="Qiushi Engine" width="260">

**Long-horizon autonomous mathematical research: from algorithm search to structural proof.**

[English report](reports/en/main.pdf) ·
[中文报告](reports/zh/main.pdf) ·
[Research materials](research/materials/README.md) ·
[Reproduce the finite proof](reproducibility/README.md) ·
[Downloads](https://github.com/Oxelra-AI/Qiushi-Engine-Matmul-Research/releases/latest) ·
[中文](README.zh-CN.md)

This project documents **Qiushi Engine's long-horizon autonomous mathematical
research** on 3 × 3 matrix multiplication over the binary field. Its outcome
is a **structural proof that every exact bilinear algorithm requires at least
21 products**, accompanied by the research trajectory, intermediate findings,
programs, and certificates from which the argument developed.

Qiushi Engine independently carried out the mathematical research end to end:
developing research routes, conducting computations, testing and correcting
claims, and constructing the proof. The report explains how accumulated
evidence and research memory informed changes of representation, turning
algorithm search into an algebraic explanation of why a 20-product algorithm
cannot exist. Both the result and the process that produced it are open to
inspection and reuse.

## The Question and the Contribution

The ordinary algorithm uses 27 products; known bilinear algorithms use 23.
A construction supplies an **upper bound**. A **lower bound** must rule out
every shorter algorithm in the specified model, not merely the candidates
a search happened to examine. Here a counted product multiplies a linear
combination of entries from the first input by one from the second. The
binary field has only 0 and 1, with addition modulo two.

This is an exact algebraic complexity question, not a measurement of CPU
instructions or GPU throughput. A small matrix can still hide a large space
of interacting decompositions. The value of this proof is that its final
obstruction explains the interaction instead of leaving a terminal
enumeration of first-factor profiles.

The central mechanism is an equality case. Certified quotient bounds force
a hypothetical 20-term decomposition into the first-factor rank profile
(16, 1, 3): sixteen first-factor matrices of rank one, one of rank two,
and three of rank three. Their rank sum is 16 + 2 + 9 = 27, exactly the
rank of a rearranged full-tensor matrix, called the split flattening.
The resulting cross-factor identities permit at most one invertible first
factor, while the profile requires three: a contradiction.

<img src="reports/en/figures/proof_structure.png" alt="Certified finite bounds and a rank budget force a saturated profile, whose cross-factor identities give a contradiction." width="900">

The diagram assumes a hypothetical 20-term decomposition over the binary
field. Certified finite premises and subsequent algebraic deductions are
separated; neither branch alone supplies the final contradiction.

The work brings together three contributions:

- **A structural proof mechanism:** finite geometry forces equality in a
  rank bound; equality couples all three factors and produces the contradiction.
- **Checkable finite premises:** eight quotient bounds with separate encoding
  and verification paths support the written mathematical argument.
- **An open research trajectory:** the documented trajectory and accompanying
  materials expose how Qiushi Engine formulated, tested, revised, and developed
  the ideas that led to the proof.

Classical matrix geometry and the inherited quotient certificate are
identified in the report.

## Research Memory and Trajectory

The report explains the system's research, knowledge, memory, and tool
capabilities at a public level. Its background is the team's
[first report on autonomous optical discovery](https://arxiv.org/abs/2604.27092).
For this mathematical research, the main computational resources were
Python and C++ research programs, numerical and symbolic calculations,
constraint solving, and exact proof verification.

**Meta-Trace is the structured research-history record within Qiushi Engine's
memory system.** It connects historical summaries, evidence, and changes of
direction. Layered summaries and retrieval let later reasoning recover the
detailed records behind earlier findings, their conditions, and corrections.
The public edition synthesizes the original Meta-Trace records with their
supporting notes, plans, programs, and results. It is organized by mathematical
question, with repetitions condensed and substantive corrections retained.
Appendix B explains the development; the [research guide](research/guide.md)
connects it to specific artifacts. Readers can study how the proof emerged,
reuse intermediate methods, and revisit unresolved questions with the earlier
evidence in view.

The open research trajectory is a contribution in its own right: it connects
the mathematical result to the evidence, corrections, and changes of
representation that produced it. Together with the executable proof package,
it makes Qiushi Engine's long-horizon autonomous research accessible to
critical study, comparison, and further development.

## How the Research Changed Direction

<img src="reports/en/figures/research_route.png" alt="Construction and finite-field explorations contribute lessons to a return to the full tensor and a structural proof." width="900">

| Observation | Change in the research question | What survived |
| --- | --- | --- |
| Numerical residuals decreased while coefficients grew | Is there a finite exact identity, rather than cancellation? | Exactness tests; no claimed rank-22 construction |
| Admissible supports did not determine the other factors | Which conditions recover a complete decomposition? | Quotient and completion methods, with unresolved branches retained |
| The full tensor supplies a rank budget | Can finite geometry force that budget to be tight? | Eight essential quotient raises and the profile (16, 1, 3) |
| The forced rank sum equals 27 | What identities follow from equality? | Cross-factor constraints and the structural contradiction |

The [research map](research/README.md) and Appendix B follow the complementary
routes and the evidence behind these changes. The useful outcome of an early
experiment could be a new representation, a counterexample, or a sharper
question. The account explains how those outcomes informed later research.

## Read the Research

| Question | Material |
| --- | --- |
| What is proved, and why? | [Main report](reports/en/main.pdf) |
| How did Qiushi Engine conduct the research? | Section 2 and the Meta-Trace in Appendix B of the [same report](reports/en/main.pdf) |
| Which routes failed or remained open? | [Research guide](research/guide.md) and [corrections](research/corrections.md) |
| Where are the notes, plans, programs and experiment records? | [Thematic material collection](research/materials/README.md) and [artifact catalog](research/catalog.json) |
| What is inherited, computed, or proved symbolically? | [Evidence map](evidence/README.md) |
| Can the finite computations be checked? | [Reproduction guide](reproducibility/README.md) |
| Is a Chinese translation available? | [Complete Chinese report](reports/zh/main.pdf), translated section by section from the English report |
| Can the documents be rebuilt? | [English sources](reports/en/README.md) and [Chinese sources](reports/zh/README.md) |

## Structure

~~~text
reports/en/       One report with integrated Meta-Trace, LaTeX sources and figures
reports/zh/       Complete Chinese translation with matching equations and original figures
research/         Guides, corrections, catalog and eight thematic material collections
proof/            Frozen finite inputs, encoders, certificates and verification
evidence/         Input identities, rendering receipts and verification scope
reproducibility/  Dependencies, commands and third-party notices
tools/            Document building, source packaging and release checks
tests/            Verification-wrapper and publication-tool regression tests
~~~

Inside proof/assets, the organization follows mathematical responsibility:
quotients, occupation, and structural verification. No live research
installation is included or required.

## Start Here

Read the [report](reports/en/main.pdf) for the argument and the
[research guide](research/guide.md) for its development. The
[release downloads](https://github.com/Oxelra-AI/Qiushi-Engine-Matmul-Research/releases/latest)
include the complete research archive with actual proof data, both PDFs,
and standalone English and Chinese LaTeX packages.

For a working Git checkout, install Git LFS and fetch the large-file contents:

~~~sh
git lfs install
git clone https://github.com/Oxelra-AI/Qiushi-Engine-Matmul-Research.git
cd Qiushi-Engine-Matmul-Research
git lfs pull
make integrity
~~~

`make integrity` checks the frozen inputs with Python 3.10 or later; it does
not run the proof. After installing the
[verification dependencies](reproducibility/README.md), use `make verify`
to reconstruct the occupation constraints and check all eight DRAT proofs.
The full replay additionally needs the documented pinned upstream verifier:

~~~sh
make verify-full
~~~

Report building is separate from mathematical verification:

~~~sh
make reports
make source-en
make source-zh
~~~

These commands rebuild both language editions and produce self-contained
LaTeX source ZIPs. Mathematical replay requires neither Qiushi Engine nor
language-model access. For an archive download, choose the named complete
research ZIP under **Releases**, rather than relying on GitHub's automatically
generated source archives to contain LFS data.
The [reuse guide](reproducibility/research-materials.md)
explains how to work with archived exploratory programs.

## Scope

The exact binary-field rank remains in **[21, 23]**. Rank-22 construction,
positive-excess decompositions, and transfer to other fields remain research
questions. The report also derives conditional restrictions on saturated
rank-22 decompositions.

The authors are listed in the report and CITATION.cff.
Original code is available under **MIT**; the original report, figures,
research records, and data are available under **CC BY 4.0**. Both permit
reuse, modification, and commercial use under their respective notice and
attribution terms. Third-party materials retain their original licenses.
See [LICENSE](LICENSE) for the scope and terms.
