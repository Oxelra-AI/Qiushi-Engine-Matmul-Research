# Meta-Trace and Research Map

Start with the [scientific guide](guide.md), then use the
[thematic materials](materials/README.md) to read the actual notes, plans,
programs, analyses and numeric inputs. The [catalog](catalog.json) identifies
every included artifact. The [correction guide](corrections.md) and
[glossary](terms.md) make historical claims and mathematical terms explicit.

Appendix B of the [unified report](../reports/en/main.pdf) presents the research
trajectory: a continuous account of Qiushi Engine's mathematical research
through its questions, representations, tests and discoveries. Section 2
introduces the system and the major changes of direction.
Its editable source is [research_record.tex](../reports/en/sections/research_record.tex).

| Route | Mathematical question | Final status |
| --- | --- | --- |
| Exact baselines | Tensor conventions, known schemes, positive controls | Foundation for later checks |
| Deformation and pairing defects | Whether a product can disappear at a finite exact point | No rank-22 witness; tested cancellation ends distinguished from solutions |
| Quotient cores | Construction through a 19-term restricted core; complete lower-bound reductions | Useful intermediate objects; exact core rank unresolved |
| Factor completion | What occupation loses about the second and third factors | Necessary conditions separated from complete decompositions |
| Symmetry | Cyclic, transpose, and mixed families; residual algebra | Scoped instruments and local evidence, not global optimality |
| Relaxations | Coding, pair correlations, moment matrices and exact cuts | No complete core exclusion |
| Full-tensor geometry | High-rank pairs, affine cosets and rank budgets | Forces profile (16, 1, 3) at length 20 |
| Saturation | Equality in split flattening and cross-factor products | Structural contradiction |
| Finite certification | Eight integer occupation exclusions and encoding semantics | CNF/DRAT artifacts with independent reconstruction paths |

Within Qiushi Engine's memory system, Meta-Trace connects historical summaries,
research evidence, and changes of direction through layered summaries and retrieval.
The public account synthesizes the original structured records with their
associated scientific artifacts, rather than simply concatenating summaries.
The [guide](guide.md#reading-the-source-materials) links its key themes to
specific notes and results. The record connects three kinds of material:
the question and proposed
approach, the calculation or argument used to test it, and the conclusion
that informed subsequent work. Substantive corrections are retained with
their consequences for later reasoning.

## Material Locations

| Need | Location |
| --- | --- |
| Follow how the mathematical questions changed | [Research guide](guide.md) and Appendix B |
| Read hypotheses, derivations and result analyses | Notes within the [eight thematic collections](materials/README.md) |
| Inspect experimental plans separately from their outcomes | Plans and result records within each collection |
| Inspect original mathematical implementations and numeric examples | Archived programs and arrays within each collection |
| Reproduce the accepted finite premises | [Maintained proof package](../proof/README.md) |
| Understand how finite checks support a mathematical implication | [Finite evidence review](finite-evidence-review.md) |
| Understand exactly what was included and checked | [Coverage](../evidence/research-coverage.json) and [reuse guide](../reproducibility/research-materials.md) |

The thematic archive is the supporting material for this integrated scientific
account. Historical experiments retain their context and status; the
maintained proof package provides the accepted finite premises and replay
commands.

## Open Questions

- Is there an exact rank-22 decomposition over the binary field?
- Can the lower bound be raised beyond 21?
- Can a related rigidity mechanism control positive rank-sum excess?
- Which parts transfer to other fields or matrix formats?

The conditional zero-excess rank-22 profiles (17, 5, 0) and (18, 3, 1)
do not answer these questions by themselves.
