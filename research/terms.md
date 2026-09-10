# Mathematical Terms

| Term | Meaning here |
| --- | --- |
| Binary field, `F2` | The field with two elements; addition and multiplication are taken modulo two |
| Bilinear algorithm | Products of a linear form in the first input with a linear form in the second input, followed by linear recombination |
| Tensor rank | The smallest number of simple tensors in an exact decomposition over the stated field |
| Upper bound | A complete exact construction using at most the claimed number of products |
| Lower bound | A proof excluding every decomposition below the claimed length |
| Brent identities | The coefficient identities expressing equality with the matrix-multiplication tensor; there are 729 entries for the `9 x 9 x 9` tensor |
| Quotient core | The tensor obtained by quotienting one factor space by a specified subspace, with an explicit coordinate convention |
| E11 core | The `8 x 9 x 9` tensor obtained by removing the first-factor direction represented by the first matrix unit |
| Occupation | The number of first factors lying in a specified subspace, counted with multiplicity |
| Completion | Supplying the remaining factors so that an admissible first-factor choice becomes an actual tensor decomposition |
| Rank profile | Counts of first-factor matrices of ranks one, two and three; distinct from the tensor rank |
| Split flattening | A rearrangement of tensor coefficients into a matrix whose rank constrains the sum of the matrix ranks of the factors |
| Saturation | Equality between the rank budget supplied by a decomposition and the rank of that rearranged matrix |
| CNF | A Boolean formula in conjunctive normal form encoding explicitly stated finite constraints |
| DRAT certificate | A proof trace checked against a specific CNF; it does not by itself establish that the CNF models the intended mathematics |
| Border-rank behavior | Approximation by low-rank tensors, potentially with unbounded decomposition coefficients; not an exact finite decomposition |
| Zero excess | The condition that the relevant matrix-rank sum exactly meets the flattening rank; conclusions conditional on it do not cover positive excess |

The [research guide](guide.md) explains why these distinctions changed the
investigation. Precise conventions and statements appear in the
[report](../reports/en/main.pdf).
