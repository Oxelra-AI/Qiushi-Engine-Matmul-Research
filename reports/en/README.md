# Unified English Report

- [Complete report](main.pdf): structural proof, background,
  Qiushi Engine's research process and computational methods, followed by
  explicit finite data (Appendix A) and the research trajectory
  (Appendix B), including the ideas, experiments, and corrections that
  shaped the research. A focused
  comparison with contemporaneous work appears only in Appendix C.
- Sole LaTeX master: main.tex. One title page, contents, page sequence and bibliography.
- Shared typography and author list: latex/.
- Editable mathematical figures and the Qiushi mark: figures/.
- Research exposition: sections/.
- References: refs.bib.

The cover uses the scientific completion date, 9 September 2026.
Subsequent editorial builds and verification receipts keep their actual
timestamps.
README images are rendered from the same TikZ sources with `make figures`.

~~~sh
make reports-en
make source-en
~~~

The reports-en target builds the unified English PDF with XeLaTeX.
The source target creates one ZIP with main.tex, its sections, bibliography
and all required figures. It rebuilds the report without private paths and
compares its PDF text with the maintained copy. The output is
dist/report-sources/qiushi-matmul-main-source.zip, relative to the repository root.

A [complete Chinese translation](../zh/main.pdf) preserves the English
section structure, mathematical statements, references and original figures.
Its [source project](../zh/README.md) is self-contained; `make reports`
builds both editions without splitting either report from its appendices.

The layout follows the Qiushi Engine BabyLM English report family.
The scientific narrative follows mathematical questions and proof mechanisms.
Section 2 introduces the public system background and mathematical environment.
The Meta-Trace connects the ideas, tests, corrections and decisions that
shaped Qiushi Engine's sustained autonomous mathematical research to the thematic research
materials.
