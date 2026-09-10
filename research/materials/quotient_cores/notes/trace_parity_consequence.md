# correction notice for analysis trace-parity/orbit interpretation

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

analysis repaired two overstatements in this note. First, the six E11 stabilizer classes are orbits of individual directions, not orbits of 19-point supports; their counts cannot replace the 255 point variables, and symmetry breaking must use a single stabilizer element acting on the whole support. Second, the fields named `forced` in older analysis JSONs mixed two notions: membership of `F(p)` in a span and absence of parity ambiguity. The valid support-level classification under a saturation guard is now `locally inconsistent / forced / free`, rebuilt in [trace_certificate_family_cuts.json](../../finite_certification/results/trace_dependency_cuts/trace_certificate_family_cuts.json) and summarized in [trace_dependency_and_symmetry_corrections.md](../../symmetry_and_residuals/notes/trace_dependency_and_symmetry_corrections.md). Pure parity rows are sound only under their certificate saturation guard and when no selected direction is in the `free` or locally inconsistent class; odd trace dependencies give the separate sound cut `sum_{q in H}(w(q)-9) >= x_p`. The older full-72 `forced_count` or six-count reduction should not be used as a theorem or as an unconditional model reduction.

# Trace-functional parity consequence from corrected multi-contraction certificates

## Setting and summary

After analysis corrected the trace coefficient convention (M_inv[c,b] not M_inv[b,c]),
the near-miss support is still rejected by a 122-row XOR certificate involving 10
saturated rank-9 contractions, but only through multi-contraction coupling (minimum
8 contractions). This ARTIFACT develops the **family-level consequence** of such certificates.

## The 9D trace functional space V_trace

All 72 rank-9 contraction trace functionals phi_q ∈ F_2^{81} span a **9-dimensional**
subspace V_trace. The Kronecker structure L(q) = Q^T ⊗ I_3 means phi_q lives in the
block-diagonal subspace (b%3 = c%3).

**Key structural fact:** the certificate's tensor functional F(p) for ALL 255 nonzero
directions lies in V_trace. This is because the certificate's tensor rows occupy only
block-diagonal (b,c) positions. Therefore the entire trace-parity analysis can be
projected into 9 dimensions.

## Parity consequence mechanism

The certificate XOR gives 0 = 1. Decomposing by terms:
- Tensor part: sum_s F(a_s)^T X_s = T_rhs_parity (= 1)
- For each term s: F(a_s) = sum_{q ∈ Q_cert_s} phi_q (zero-coefficient condition)
- Trace equations: phi_q^T X_s = 1 for participating saturated q
- Therefore: F(a_s)^T X_s = |Q_cert_s| mod 2

The contradiction is: sum_s |Q_cert_s| mod 2 = 6 ≡ 0 ≠ 1 = T_rhs_parity.

## Parity well-definedness

**Critical issue:** when the trace generators for a direction p have dependencies,
the decomposition F(p) = sum alpha_q phi_q is not unique, and the forced value
(= sum alpha_q mod 2) is ambiguous.

Tested result:
- **Cert-only guard (10 contractions):** 246/255 well-defined, 9 ambiguous
- **Full-72 guard (all 72 rank-9):** Only 9/255 well-defined, 246 ambiguous!

The full-72 guard is useless for parity consequence because its massive generator
dependencies make almost every forced value ambiguous. The cert-only guard is
much better because 10 contractions create few dependencies.

## 9 hitting-span rank-deficient directions

Under the full-72 guard, 9 directions have hitting-phi span rank = 8 (not 9):
{5, 6, 7, 33, 34, 35, 37, 38, 39}

In matrix terms (E11-deleted coordinates):
- E12+E21, E13+E21, E12+E13+E21
- E12+E31, E13+E31, E12+E13+E31  
- E12+E21+E31, E13+E21+E31, E12+E13+E21+E31

These are exactly the nonzero matrices supported on {E12,E13} × {E21,E31}
with at least one entry in each factor — the "cross" of the deleted E11 direction.
Of these, 4 have F(p) outside the 8D hitting span (full-72 escape): {5, 7, 33, 35}.
These correspond to the "E12-containing" directions in the cross.

## Multi-certificate coverage

Generated certificates for 8 trace-inconsistent supports:
- 7/8 give self-contradictions through parity
- **212/255 directions have varying forced values across certificates**: different
  certificates capture genuinely different algebraic structure
- Only 18/255 directions are forced by ALL certificates simultaneously
- Cross-certificate parity contradictions exist (cert[i] rejects support[j])

## Family consequence statement

**Theorem (conditional).** Fix a corrected trace certificate C with tensor functional F
and certificate contractions Q_C. For any distinct 19-point E11-core A-support S where:
(a) all contractions in Q_C are saturated (weight = 9),
(b) all 19 directions are parity-well-defined under Q_C,
(c) all 19 F(p) are in span{phi_q : q ∈ Q_C, q(p)=1},
the forced parity sum must equal T_rhs_parity(C).

The near-miss satisfies (a)-(c) with forced sum 0 ≠ 1 = T_rhs. Multiple certificates
give multiple independent constraints on different support families.

## Limitations

- The parity consequence is a SHADOW of the full certificate — it captures the modular
  constraint but not the full linear-algebraic structure. Some trace-inconsistent
  supports (like cert[3]) have matching parity but are still contradicted by the
  full certificate.
- Each certificate's guard is specific: it requires particular contractions to be
  saturated. Different supports have different saturation patterns.
- The 9D V_trace projection loses 72 dimensions of X_s freedom. The rank-one
  constraint on X_s is not captured by trace equations alone.
- The parity consequence alone cannot prove R_{F2}(core) >= 20. It would need to
  combine with Wang occupation, domains, transversality, and exact completion.

## Implications for the E11 distinct branch

1. **The corrected trace mechanism provides genuine B/C compatibility information**
   beyond Wang occupation, rejecting 15/31 stored near-misses.

2. **The parity consequence gives conditional, well-defined family constraints** from
   each certificate. These can serve as additional cuts in SAT/CP-SAT models.

3. **The 9D V_trace representation is the natural compact framework** for the trace
   approach. But it needs to be used under cert-specific guards (10 contractions),
   not the full-72 guard, because of parity ambiguity.

4. **The 9 rank-deficient directions form a structurally distinguished family** related
   to the E11 "cross." Their special role should be investigated further.

5. **The critical open question remains:** does the combined Wang + trace + domain +
   completion system have ANY satisfying 19-point distinct support? The parity
   consequence narrows the search but doesn't resolve it.

## Files produced

- [family_consequence.py](../code/family_consequence.py): cert-only and full-72 forced analysis
- [vtrace_perp.py](../code/vtrace_perp.py): V_trace perpendicular structure
- [multi_cert_coverage.py](../code/multi_cert_coverage.py): multi-certificate generation
- [9d_vtrace.py](../code/9d_vtrace.py): 9D V_trace basis analysis
- [parity_welldef.py](../code/parity_welldef.py): parity ambiguity diagnosis
- `workspace/data/family_consequence/`: all output JSONs
