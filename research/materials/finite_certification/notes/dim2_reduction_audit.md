# dim-2 reduction audit

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

The audit recomputed 3x3 matrix ranks for every nonzero element of each recorded dim-2 Wang orbit representative, using `cert_profile.json` and the local occupation overlay from `dim3_raises_to_dim2.json`.
Relevant dim-2 orbits (at least two nonzero rank>=2 elements): [479, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491].
Irrelevant for the two-high-rank-generator reduction: [478, 480].
Relevant orbits still below lower bound 19 after the local occupation overlay: [481, 482, 483].

| index | basis | ranks of nonzero elements | old LB | overlay LB | relevant | occupation status |
|---:|---|---|---:|---:|---|---|
| 478 | ['0x1', '0x2'] | [1, 1, 1] | 17 | 18 | False | INFEASIBLE |
| 479 | ['0x1', '0xa'] | [1, 2, 2] | 18 | 19 | True | INFEASIBLE |
| 480 | ['0x1', '0x10'] | [1, 1, 2] | 18 | 18 | False | OPTIMAL |
| 481 | ['0x1', '0x14'] | [1, 2, 2] | 18 | 18 | True | OPTIMAL |
| 482 | ['0x1', '0x54'] | [1, 3, 3] | 18 | 18 | True | OPTIMAL |
| 483 | ['0x1', '0xa0'] | [1, 2, 3] | 18 | 18 | True | OPTIMAL |
| 484 | ['0xa', '0x13'] | [2, 2, 2] | 18 | 19 | True | INFEASIBLE |
| 485 | ['0xa', '0x14'] | [2, 2, 2] | 18 | 19 | True | INFEASIBLE |
| 486 | ['0xa', '0x44'] | [2, 2, 2] | 18 | 19 | True | INFEASIBLE |
| 487 | ['0xa', '0x54'] | [2, 3, 3] | 18 | 19 | True | INFEASIBLE |
| 488 | ['0xa', '0x60'] | [2, 2, 3] | 18 | 19 | True | INFEASIBLE |
| 489 | ['0xa', '0x102'] | [2, 2, 2] | 18 | 19 | True | INFEASIBLE |
| 490 | ['0xa', '0x113'] | [2, 3, 3] | 18 | 19 | True | INFEASIBLE |
| 491 | ['0x54', '0xa3'] | [3, 3, 3] | 18 | 19 | True | INFEASIBLE |

Mathematical use: if a length-20 full decomposition existed, the full A-slot flattening gives sum(rank(a_t)-1)>=7. Thus there are at least four rank>=2 A-factors. Pick one as p. If another term has the same A-direction p, quotienting by <p> removes at least two terms and leaves length <=18, contradicting the recorded one-dimensional Wang lower bound 19. Otherwise choose an independent rank>=2 A-factor a; quotienting by W=<p,a> removes two terms and leaves length <=18. Therefore the remaining lower-bound work is exactly to establish lower bound 19 for the relevant dim-2 quotient orbits not already raised by the occupation overlay.
