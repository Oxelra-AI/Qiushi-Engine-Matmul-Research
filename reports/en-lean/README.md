# Research Report with Lean Formalization

[English PDF](main.pdf) | [Chinese edition](../zh-lean/main.pdf) | [LaTeX master](main.tex)

This edition integrates the completed Lean proofs with the structural argument,
computational verification, and research trajectory. The original mathematical
argument, author list, bibliography, and figures are retained, with statement
conditions aligned to the formal proofs.

`main.tex` is the sole master and includes all three appendices. `latex/`,
`sections/`, `figures/`, and `refs.bib` form a self-contained XeLaTeX project.
Build within this directory:

```sh
latexmk -xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The [formalization coverage](../../formalization/COVERAGE.md) records the precise
statements and hypotheses; the [Lean guide](../../formalization/README.md)
describes proof reproduction. Lean integer branch certificates and the original
CNF/DRAT artifacts are distinct verification routes.

This edition is separate from the [original English report](../en/main.pdf).
Its build receipt is [lean-report-build.json](../../evidence/lean-report-build.json).
