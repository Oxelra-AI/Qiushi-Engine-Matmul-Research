# decode correction: withdraw analysis zero-survivor rep2 closure

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Corrected evidence state

The analysis zero-survivor claim for the rep2 adjacent-pair prefix `{1,2}` is **withdrawn**.  The diagnostic scripts `verify_zero_survivor.py` and the LUT-scanning part of `ruling_line_transport.py` reimplemented Wang LUT key decoding incorrectly.

Canonical encoding, as in [wang_capacity_lazy.py](../../occupation_and_completion/code/wang_capacity_lazy.py), is:

- `d = key & 0xF` stores the subspace dimension;
- the basis vectors start at `key >> 4`;
- exactly `d` nine-bit vectors are read.

The analysis diagnostic instead read nine-bit chunks from bit zero until the key was exhausted.  This mixed the dimension nibble into the first vector and shifted every later vector boundary.  Consequently the reported bases, dimensions, span memberships, and all zero-survivor counts in [summary.json](../../quotient_cores/results/ruling_line/diagnostic/summary.json) are invalid.

## Decisive key check

For the key cited in analysis:

- key `0x11945003` has canonical dimension `3` and canonical basis `[256, 162, 70]`;
- `rref_key(unpack_basis(key)) == key`;
- the correct span contains neither point `1` nor point `2` nor point `100`;
- the broken decoder produced `[3, 40, 101, 2]`, the false source of the alleged repeated-pivot example.

The full-LUT canonical audit in [corrected_decode_and_rep2_base.json](../results/decode_correction/corrected_decode_and_rep2_base.json) found:

- `roundtrip_all_ok: true` over all 8,283,458 LUT entries;
- zero duplicate-pivot examples in canonically decoded bases;
- prefix `[1,2]` has `0` residual-0 vertex exclusions and `509` survivors under the correct decoder;
- prefix `[1,2,3]` has `372` residual-0 vertex exclusions and `136` survivors, agreeing with the earlier analysis marked-prefix profile rather than the analysis diagnostic.

Thus the old graph/pivot path was not refuted.  `make_pivot_dict` assumes its input basis is already canonical/RREF; that assumption is satisfied when bases come from `wang_capacity_lazy.unpack_basis` applied to the LUT.  It would be unsafe on arbitrary non-echelon lists, but that is not what the checked pipeline used.

## Consequences for the proof route

- Do **not** count the adjacent-pair/rep2 branch as closed.
- Do **not** rebuild the matching search around the false zero-survivor result.
- Do **not** use [summary.json](../../quotient_cores/results/ruling_line/diagnostic/summary.json) or the analysis note as proof evidence.
- Previously DRAT-verified matching and fixed-prefix proof objects remain valid; this correction does not weaken those checked UNSAT certificates.
- The valid analysis local proof remains: fixed prefix `[1,2,3]` is excluded by the promoted Wang formula with exact regeneration and DRAT replay.  Its group transport gives the 98 ruling-line triple exclusions as derived constraints.  Those constraints should be resumed as additional proof-backed structure for the rep2 branch, not declared redundant.
