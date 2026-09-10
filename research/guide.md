# From Algorithm Search to a Structural Obstruction

The research began with a constructive question: can the matrix-multiplication
tensor be written using fewer than 23 simple tensors? It ended with a different
kind of understanding: in the binary field, the structure of a hypothetical
20-term decomposition forces incompatible identities.

Qiushi Engine reached this result through changes in what its mathematical
representations retained, what they discarded, and what an exact conclusion
would require. The public Meta-Trace follows those changes and their evidence.

## The Questions That Changed the Research

| Question | What was learned | Where to study the evidence |
| --- | --- | --- |
| Does a small numerical residual describe an exact shorter algorithm? | Coefficients can grow while large terms cancel. A finite exact identity requires more than convergence of the residual. | [Deformation and incidence](materials/deformation_and_incidence/README.md) |
| Can a smaller quotient expose the missing algorithm? | Removing one first-factor direction gives a useful core and an explicit lift-back construction. The converse needs separate coverage arguments. | [Quotient cores](materials/quotient_cores/README.md) |
| Do admissible first-factor counts specify a decomposition? | Occupation inequalities forget the coupled second and third factors. Support feasibility and complete factorization are different questions. | [Occupation and completion](materials/occupation_and_completion/README.md) |
| Does symmetry make the unrestricted question finite and manageable? | Symmetry yields informative families and residual algebra, but exclusion of a family does not settle the whole tensor. | [Symmetry and residuals](materials/symmetry_and_residuals/README.md) |
| Can stronger numerical relaxations close the remaining gap? | Moment, count and cut formulations expose obstructions and also reveal conditionality and integrality gaps. | [Relaxations and cuts](materials/relaxations_and_cuts/README.md) |
| What is lost by remaining inside one core? | The full tensor has a rank budget that connects otherwise separate factors. | [Full-tensor structure](materials/structural_obstruction/README.md) |
| What happens when this budget is exactly exhausted? | Equality in the split flattening produces product identities, not merely another scalar inequality. | [Structural argument](../reports/en/main.pdf) |

Exact baseline controls and independent finite certification support every
transition. Their function is to distinguish a genuine mathematical obstacle
from a convention, decoding or encoding error.

## The Final Argument

Over the binary field, certified quotient inequalities constrain every proposed
20-term decomposition. Eight additional two-dimensional quotient bounds restrict
the possible high-rank first factors. Affine matrix geometry and the full-tensor
rank budget then force the profile `(16, 1, 3)`.

The associated sum of matrix ranks is `16 + 2 + 9 = 27`, equal to the rank of
the split flattening. Equality forces orthogonal-idempotent relations. For the
matrix-multiplication tensor, a cross-factor product identity makes two
invertible first factors incompatible, whereas the forced profile contains
three. This is the contradiction proving the lower bound 21.

The [proof package](../proof/README.md) holds the finite inputs and replayable
certificates. The [report](../reports/en/main.pdf) supplies the mathematical
definitions, deductions and the connection between each finite computation
and the mathematical conclusion it supports.

## Following the Research Decisions

For each route, read the notes for the question and proposed method, then
the programs and results for its test, and the subsequent analysis for what
changed. The [correction guide](corrections.md) identifies conclusions that
were narrowed or replaced. This reading connects an experiment to the next
decision rather than considering its output in isolation.

This organization shows how Qiushi Engine accumulated mathematical understanding:
an unsuccessful construction route could still supply a useful representation,
an invalid inference could reveal a necessary control, and a relaxed counting
problem could point toward a structural equality case. The integrated account
preserves these dependencies while the thematic collections provide the
material needed to examine them.

## Reading the Source Materials

The public Meta-Trace is a thematic synthesis of original structured research
records, checked against the associated scientific notes and results. It
combines recurring accounts, preserves consequential corrections, and links
related questions without presenting concurrent explorations as a single
chronological sequence. These examples connect the account to concrete material:

| Development in the account | Supporting research material |
| --- | --- |
| Falling residuals can conceal divergent coefficients | [Cancellation analysis](materials/deformation_and_incidence/notes/cancellation_degeneration.md) and [corrected interpretation](materials/deformation_and_incidence/notes/corrected_cancellation.md) |
| The core-to-full bridge needs an exact map and scope | [Core bridge review](materials/quotient_cores/notes/core_bridge_review.md) |
| An encoding error invalidated an apparent lower bound | [Auxiliary-variable correction](materials/finite_certification/notes/seqcounter_error.md) |
| Restricted symmetry results do not settle unrestricted rank | [Symmetry review](materials/symmetry_and_residuals/notes/review_symmetry_and_next_attack.md) |
| Stronger relaxations still left the core problem open | [Pooled square-cut analysis](materials/relaxations_and_cuts/notes/pooled_square_cuts_analysis.md) |
| Returning to the full tensor supplied the rank budget | [Flattening and formulation](materials/structural_obstruction/notes/flattening_bound_and_formulation.md) |
| Pairwise constraints became affine geometry | [Structural coset reduction](materials/structural_obstruction/notes/structural_coset_reduction.md) |
| Equality replaced terminal enumeration with factor identities | [Short saturated route](materials/structural_obstruction/notes/short_saturated_lower_bound_route.md) and [elementary product check](materials/quotient_cores/results/structural/product_formula_full_elementary_matrix_check.json) |
| Finite premises and the written proof were brought together | [Theorem-chain review](materials/structural_obstruction/notes/theorem_chain_review.md) and [maintained replay](../proof/README.md) |

The accepted proof determines the status of the theorem. Historical records
also retain exploratory claims that were later corrected; read them with the
[correction guide](corrections.md). Their scientific value includes the
questions, counterexamples, and changes of representation that informed later
work, not just the conclusions that appear in the final proof.

## What Remains Open

The result establishes `21 <= R_F2(T_333) <= 23`. The exact rank and transfer
to other fields remain open. The conditional zero-excess rank-22 profiles
`(17, 5, 0)` and `(18, 3, 1)` leave positive-excess cases unresolved.

The important reusable ideas are the separation of support from completion,
explicit maps between cores and the full tensor, and the use of equality in
a rank bound to extract algebraic identities. Their scope must be established
afresh when applied to another tensor or field.
