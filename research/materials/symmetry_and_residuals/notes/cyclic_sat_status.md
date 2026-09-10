# Cyclic-invariant SAT search — status and next steps

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## What was built
1. **Tseitin CNF encoder** ([cyclic_sat_f2.py](../code/cyclic_sat_f2.py)): encodes cyclic-invariant Brent equations for any skeleton (f,m) with f+3m=r over F_2 as DIMACS CNF with AND3 Tseitin gates + XOR chain. Includes symmetry breaking (cube lex, orbit lex, within-orbit Z/3 canonical).
2. **CryptoMiniSat5 native-XOR encoder** ([cms_cyclic_sat.py](../code/cms_cyclic_sat.py)): replaces Tseitin XOR chains with native `x` clauses for CMS Gaussian elimination. Reduces from ~16K vars / ~53K clauses to ~10-11K vars / ~31-33K regular + 249 XOR clauses.
3. **Quotient span analysis** ([quotient_span.py](../../quotient_cores/code/quotient_span.py)): computes the F_2 orbit quotient image span in the 84-dim quotient E_inv/Sym^3.

## What was verified
- **Encoding correctness**: rank-27 positive controls (3,8), (0,9), (6,7), (9,6) all SAT with 0 Brent errors, confirming the encoder.
- **Sym^3 quotient**: dim=84, q(T333) HW=8, T333 ∉ Sym^3. Full span rank 84 reached after only 88 random orbit samples → no quotient-span algebraic obstruction exists.
- **SAT solver difficulty**: both Kissat 4.0.4 and CaDiCaL 3.0.0 time out at 120-300s on all rank-22 skeletons (tested (1,7) and (10,4)) with both Tseitin and CMS encodings. CryptoMiniSat5 also timed out at 300s on (10,4) with native XOR.

## Available SAT tools
- kissat 4.0.4, cadical 3.0.0, drat-trim (at $QIUSHI_TOOLS_ROOT/bin/)
- cryptominisat5 (at /usr/bin/)
- PySAT (pysat.solvers)
- SageMath (at $QIUSHI_TOOLS_ROOT/bin/sage)

## Key encoding sizes
| Skeleton | Primary vars | Tseitin total | CMS total | Reg clauses | XOR clauses |
|----------|-------------|---------------|-----------|-------------|-------------|
| (1,7)    | 198         | ~16K/~53K     | 11080     | 33450       | 249         |
| (10,4)   | 198         | ~15K/~51K     | 10324     | 31020       | 249         |
| (22,0)   | 198         | ~16K/~53K     | —         | —           | 249         |

## What remains
The rank-22 cyclic F_2 SAT instances are **decidable but hard** for current CDCL/Gauss solvers at 300s. Options:
1. **Longer timeouts** (1800s+ per skeleton, 8 skeletons)
2. **Cube-and-conquer** (lookahead cubing + CDCL)
3. **SageMath Gröbner basis** computation over GF(2) for the 198-variable degree-3 system
4. **Direct F_2 algebraic search**: enumerate cubes (511 options), use linear algebra to check orbit feasibility
5. **flip-cpd** or other specialized tensor decomposition tools in cyclic-invariant coordinates

## Files
- `data/cyclic_sat/`: CNF files, rank-27 results, quotient analysis
- [cyclic_sat_f2.py](../code/cyclic_sat_f2.py): Tseitin encoder with symmetry breaking
- [cms_cyclic_sat.py](../code/cms_cyclic_sat.py): CMS native-XOR encoder
- [quotient_span.py](../../quotient_cores/code/quotient_span.py): quotient span analysis
