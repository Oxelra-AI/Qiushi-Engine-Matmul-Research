# Connecting Finite Evidence to the Theorem

Three checks separate a successful computation from a valid finite premise:
the tensor convention must be right, the enumeration must cover the stated
objects, and the encoding must express the intended integer constraints.
This note collects the mathematical content of the final evidence review.
The maintained [reproduction guide](../reproducibility/README.md) specifies
which of these checks a requested replay actually performs.

## Reconstructing the Quotient Table

An independently written C++ expansion starts from the pinned certificate's
496 representatives. Elementary left and right transvections and transpose
generate the relevant actions, with compensating actions on the other tensor
factors checked against the tensor convention.

The expanded table has 8,283,458 subspaces, with dimension counts

```text
1, 511, 43435, 788035, 3309747, 3309747, 788035, 43435, 511, 1.
```

The recorded comparison found no missing keys or value mismatches with the
stored table. This establishes agreement with an independent expansion of
the certified representatives, not an independent rediscovery of the
inherited lower bounds.

## Coverage and Integer Semantics

Independent orbit formation enumerates all 43,435 two-dimensional subspaces
of the nine-dimensional binary vector space. It finds 14 orbits; the
all-high-rank subspaces are precisely the eight representatives 484--491,
with 32,018 members in total.

For each of those eight quotients, the occupation system at total 18 is
encoded and its UNSAT certificate checked. The mathematical implication
must cover decompositions of length at most 18, not merely a convenient
exact-length formulation. The report includes the exact-total justification.
The inherited quotient lower bound is 18; the new certified exclusion raises
it to 19. These two statements must not be conflated.

Length-19 occupation vectors are useful positive controls. In particular,
valid controls for representatives 486 and 489 have multiplicity two.
Replacing integer counts by a Boolean presence indicator would therefore
overconstrain the intended problem. These are occupation controls, not
complete length-19 tensor decompositions.

The primary Boolean-copy encoding and the separate transparent unary route
are preserved in the [proof package](../proof/README.md). Checking a certificate
proves UNSAT for a formula; independent row reconstruction and the forward map
from a legal occupation vector establish why that formula is relevant.

## Scope of the Structural Implication

The affine-geometric argument uses four-point planes in `AG(3,2)`. Any five
distinct points contain a plane: ten pair sums occupy only seven nonzero
values, and a collision gives disjoint pairs with the same sum. A formulation
in terms of three-term arithmetic progressions would be inappropriate here.

The rank-sum excess is the sum of first-factor matrix ranks minus 27. It is
not the sum of rank minus one for each term. Equality in the former quantity
is what permits the saturated product identities.

The cyclic tensor symmetry in the report's convention is
`(A, B, C) -> (B, C^T, A^T)`. It transfers the corresponding saturation
statement across factors. Matrix rank is invariant under transpose, but that
alone would not justify using an incorrect tensor action.

Finally, the argument proves a lower bound of 21, not optimality at 21.
Its symbolic deductions need no further search once the certified finite
premises are granted; they are not independent of those premises.
