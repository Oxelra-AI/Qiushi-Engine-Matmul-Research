# Jennrich/Strassen commutator note — superseded scope

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This file is retained only as a historical record of the first commutator calculation. Its original universal `(10,4)` exclusion was withdrawn in earlier analysis.

Current reliable content:

1. For a fixed cubic residual with nondegenerate Hessian form, the Strassen/Hessian commutator bound gives a pointwise rank obstruction to low Waring rank. In the BILR residual, exact integer directions give a rank-4 commutator, so the fixed BILR residual has Waring rank at least 11.
2. The fixed BILR residual also has an explicit 11-cube expression, and analysis gave an independent Koszul--Young flattening certificate; hence the fixed BILR residual has Waring rank exactly 11.
3. This does **not** prove that every rank-4 exterior decomposition of the Cartan trivector gives a residual of Waring rank at least 11. Internal determinant-one frame changes inside each exterior plane preserve the exterior volume but change the symmetric residual cubic.
4. The trace-form signature is indefinite, so the scalar `Phi=2 tr(C^4)-tr(C^2)^2` is only a nonzero certificate for rank at least 4. The exact equations for rank at most 2 are the 4x4 Pfaffians of `Omega=K[H_X,H_Y]`.
5. analysis further showed that the reduced-pair orthogonal-complement test is inactive at the BILR identity frame: all six reduced split commutators vanish there. This blocks the proposed cheap two-frame elimination at BILR.

Use instead:

- [jennrich_corrected_scope.md](jennrich_corrected_scope.md)
- [product_commutator_instrument.md](product_commutator_instrument.md)
- [associator_lemma_and_certificate.md](associator_lemma_and_certificate.md)
- [pfaffian_certificate_and_scan.json](../results/pfaffian_certificate/pfaffian_certificate_and_scan.json)
- [bilr_reduced_pair_calibration.json](../results/reduced_pair_associator/bilr_reduced_pair_calibration.json)
- [bilr_common_pencil_certificate.json](../results/reduced_pair_associator/bilr_common_pencil_certificate.json)

The pure cyclic `(10,4)` branch, other exterior components, and nontraceless `m>=5` branches remain open; no statement in this historical file should be used as a global rank-22 exclusion.
1. **ker Ψ ≠ 0 branch (m ≥ 5):** nontraceless free orbits with degenerate
   exterior summands can evade the trace-grading argument. The skeletons
   (7,5), (4,6), (1,7) need the full s¹, s², s³ equations and
   decomposable-bivector analysis.

2. **Non-cyclic rank-22 decompositions:** the saturated independent-UV
   incidence remains the global formulation.

3. **Exact document:** the results from Cartan rank-4 through the Jennrich
   certificate form an independently verifiable body of mathematics that
   should be written as a formal proof.

## Evidence files
- [hessian_gl3_instrument.py](../code/hessian_gl3_instrument.py): gl₃ commutator instrument
- [jennrich_integer_cert.py](../code/jennrich_integer_cert.py): exact integer certificate
- [hessian_gl3_bilr.json](../results/hessian_commutator/hessian_gl3_bilr.json): gl₃ BILR data
- [jennrich_integer_certificate.json](../results/hessian_commutator/jennrich_integer_certificate.json): certificate
- [ten_cube_commutator_tests.json](../results/hessian_commutator/ten_cube_commutator_tests.json): 10-cube tests
