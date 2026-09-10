# Corrections and Mathematical Status

The historical materials record evolving understanding. This guide identifies
the principal corrections that matter when interpreting them. The maintained
report and final proof package govern the accepted result.

| Earlier interpretation | Correction | Consequence |
| --- | --- | --- |
| Small residual and shrinking singular value indicate a rank-22 algorithm | Divergent coefficients can produce cancellation without a finite exact decomposition | Numerical trajectories are experiments, not exact witnesses |
| A first-factor restriction bound gives a halfspace capacity | Occupation counts the appropriate killed subspace and its multiplicities | The original overconstrained capacity infeasibility is invalid |
| An UNSAT cardinality encoding proves a new global lower bound | Auxiliary-variable collisions can make the encoding itself contradictory | The earlier claim was withdrawn; it is not a premise of the accepted proof |
| A quotient lookup row can be reused with another coordinate decoding | The quotient map and decoding must agree exactly | Apparent exclusions based on a mismatched map were withdrawn |
| A branch-dependent constraint can be applied globally | Prefix and lift assumptions must accompany the constraint | Local exclusions do not prove unrestricted impossibility |
| A feasible occupation support is a decomposition | The second and third factors must satisfy the complete tensor identities | Necessary-condition candidates are not algorithms |
| One residual, symmetry family or frame rules out all rank-22 schemes | Fixed representatives and restricted families have limited coverage | Local algebraic results remain scoped |
| Vanishing of a scalar commutator invariant characterizes rank at most two | The full Pfaffian conditions are needed in the relevant indefinite setting | The scalar remains only a one-directional obstruction |
| A normalized moment witness or square cut automatically has the intended interpretation | Normalization, exact reconstruction and validity assumptions require checks | Corrected cuts are distinguished from the superseded formulas |
| A lower bound for one core immediately transfers to every full decomposition | Reduction, symmetry transport and branch coverage must all be justified | The full-tensor theorem requires its complete implication chain |

## How to Use Historical Results

Documents under materials/ are research records, not a second authoritative
proof. A JSON field such as `verified`, `status`, `unsat` or `all_ok` is a saved
statement by the original computation. The release catalog marks these records
as historical and does not reinterpret those fields as a fresh check.

For the accepted finite premises, use [the maintained verifier](../proof/README.md).
It requires a successful new process and valid newly produced output. For the
symbolic argument, use the [report](../reports/en/main.pdf). For prospective
experiments, preserve the distinction between a proposed test, a result under
its explicit assumptions, and a theorem covering all target cases.

The fact that a historical route was corrected does not make every calculation
on that route invalid. Conversely, a later correct theorem with the same
numerical value does not validate an earlier invalid proof.
