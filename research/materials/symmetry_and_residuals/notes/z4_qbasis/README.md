# Z4 Q-basis data

> Historical research record. Read with the [correction guide](../../../../corrections.md); recorded conclusions are not new verification receipts.

Authoritative analysis artifacts:

- `qbasis_selftest.json`: canonical Q-basis convention and target/BILR self-tests. This fixes the packed-pairing issue.
- `symbolic_orbit_formula.json`: symbolic identities for length-four and length-two Z4 cube orbits and the hidden tail scaling `h=eps*t^{-6}`.
- `tail_positive_control_bilr_v2.json`: BILR positive control with the hidden tail scalars included. This supersedes the earlier tail analyzer for interpreting the BILR tail.
- `bilr_tail442_groebner.json`: exact modular fixed-BILR-residual test showing the generic-branch `4+4+2` tail equations are empty over `F_65521` in both `q0=1` and `q1=1` charts for all 32 variants. This is a fixed-residual control; analysis's Koszul--Young flattening remains the stronger proof for the BILR residual.

Caution:

- `generic_extractor_bilr_positive.json` and `tail_branch_analyzer_bilr.json` were intermediate debugging artifacts. They were useful for discovering that the off-block extraction misses the tail scaling, but their original interpretation of the tail is incomplete. Do not use them as evidence for a rank-22 exclusion. Use `tail_positive_control_bilr_v2.json`, `symbolic_orbit_formula.json`, and `bilr_tail442_groebner.json` instead.
