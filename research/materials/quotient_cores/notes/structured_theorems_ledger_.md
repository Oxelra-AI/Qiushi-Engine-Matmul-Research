# Structured theorem ledger after analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This ledger preserves the mathematically durable results that are already supported by notes, scripts, JSON data, or replayable certificates. It is not a final paper and not a substitute for the unresolved rank determination of `T_333`. Its purpose is to make the original, scoped results independently writable and to keep withdrawn arguments from contaminating later proofs.

## Global status

No exact rank-22 algorithm has been found. No unrestricted characteristic-zero or finite-field proof of rank 23 optimality has been established. The reliable global finite-field interval remains
\[
20\le R_{\mathbb F_2}(T_{333})\le 23.
\]
The field-independent global formulation still asks whether the nine-dimensional `UV` slice space `L` lies in a 22-dimensional subspace spanned by rank-one `9 x 9` matrices.

## Proven or strongly supported scoped results

### 1. Independent-UV refinement and rank-one-span formulation

**Statement.** Over any field, every rank-`<=22` decomposition of `T_333` can be converted to a presentation with exactly 22 independent `UV` columns by shortening along `UV` relations and splitting terms until the count reaches 22. Consequently
\[
R_K(T_{333})\le r
\iff
L\subseteq \operatorname{span}\{x_1,\ldots,x_r\},
\]
where each `x_i` is a rank-one element of `K^9 \otimes K^9` and `L` is the nine-dimensional `UV` slice space. For `r=22`, the quotient condition is a 13-plane in `E/L`.

**Evidence/proof carriers.** [independent_uv_refinement_and_blaser_status.md](../../deformation_and_incidence/notes/independent_uv_refinement_and_blaser_status.md), [completion_chart_results.json](../../deformation_and_incidence/results/completion_chart/completion_chart_results.json), [f2_span_oracle_results.json](../results/f2_span_oracle/f2_span_oracle_results.json).

**Scope.** This is a global reformulation, not a rank lower bound by itself. Singular or nontransverse presentations are not discarded; the refinement is algebraic.

### 1b. Trace-graded cyclic theorem with explicit tracelessness hypothesis

**Statement.** For a characteristic-zero pure cyclic rank-22 decomposition $f+3m=22$ of $T_{333}$ whose free orbit representatives are traceless: the $s$-grading of $X=X_0+sI$ in the diagonal identity gives $\operatorname{tr}(X_0^2)=\sum_{i=1}^f c_i\lambda_i^2$ on $\mathfrak{sl}_3$, where the Killing form has rank 8. Since each $c_i\lambda_i^2$ has rank $\le1$, this forces $f\ge8$, hence $m\le4$. Combined with the Cartan prehomogeneity $m\ge4$ (result 4 below), a pure cyclic rank-22 decomposition with traceless free orbits has skeleton $(10,4)$.

**Three moment equations in the traceless case.** The cube traces/evaluations $c_i=\ell_{L_i}(I)$ and restricted forms $\lambda_i=\ell_{L_i}|_{\mathfrak{sl}_3}$ satisfy: (s¹) $\sum c_i\lambda_i^2=\operatorname{tr}(X_0^2)$ on $\mathfrak{sl}_3$ (rank-8 trace form, det $-3$; the standard Killing form is a scalar multiple); (s²) $\sum c_i^2\lambda_i=0$ in $\mathfrak{sl}_3^*$; (s³) $\sum c_i^3=3$ when fixed-cube scalar coefficients have been absorbed, and more generally with weights $\rho_i c_i^3$. With normalized $\mu_i=\lambda_i/c_i$ and $w_i=\rho_i c_i^3$, these become $\sum w_i=3$, $\sum w_i\mu_i=0$, $\sum w_i\mu_i\otimes\mu_i=K$. In a hypothetical $(10,4)$ solution, exactly 8 active nodes are impossible because eight active $\mu_i$ would form a basis and the nonzero-weight relation $\sum w_i\mu_i=0$ could not hold; therefore $k=9$ or $10$ active nodes.

**Tracelessness mechanism.** The target's $I\wedge\Lambda^2(\mathfrak{sl}_3)$ antisymmetric component is zero ($\operatorname{tr}([B,C])=0$), so free orbit traces satisfy a 28-equation linear system $\Psi=0$ from the trace-parameter space. If every $P_j=\langle u_j,v_j,w_j\rangle$ is three-dimensional, $\Psi$ factors through isomorphisms $K^3\simeq\Lambda^2(P_j)$ and injectivity of $\Phi:\bigoplus_j\Lambda^2(P_j)\to\Lambda^2(\mathfrak{sl}_3)$ forces all traces to vanish. In degenerate branches one must use $\Psi$ directly.

**Evidence/proof carriers.** [trace_grading_collapse.py](../../symmetry_and_residuals/code/trace_grading_collapse.py), [trace_grading_verification.json](../../symmetry_and_residuals/results/trace_grading/trace_grading_verification.json), [cube_moment_analysis.py](../../symmetry_and_residuals/code/cube_moment_analysis.py), [cube_moment_analysis.json](../../symmetry_and_residuals/results/trace_grading/cube_moment_analysis.json), [trace_grading_collapse.md](../../symmetry_and_residuals/notes/trace_grading_collapse.md), plus analysis repairs [moment_cubature_instrument.py](../../relaxations_and_cuts/code/moment_cubature_instrument.py), [moment_cubature_instrument.json](../../relaxations_and_cuts/results/moment_cubature/moment_cubature_instrument.json), [nine_node_reflection_cubature.py](../code/nine_node_reflection_cubature.py), [nine_node_reflection_cubature.json](../../relaxations_and_cuts/results/moment_cubature/nine_node_reflection_cubature.json), [cubic_residual_control.py](../code/cubic_residual_control.py), [cubic_residual_control.json](../../relaxations_and_cuts/results/moment_cubature/cubic_residual_control.json), [nontraceless_branch_checks.py](../code/nontraceless_branch_checks.py), [nontraceless_branch_algebra.json](../../relaxations_and_cuts/results/moment_cubature/nontraceless_branch_algebra.json), [plane_invariant_extractor.py](../code/plane_invariant_extractor.py), [bilr_plane_invariants.json](../../symmetry_and_residuals/results/plane_invariants/bilr_plane_invariants.json), [bilr_phi_minor.py](../../symmetry_and_residuals/code/bilr_phi_minor.py), [bilr_phi_rank12_minor.json](../../symmetry_and_residuals/results/plane_invariants/bilr_phi_rank12_minor.json).

**BILR positive control (exact).** At the BILR rank-4 exterior component, $\Phi$ has rank 12, so traces vanish component-locally under plane-preserving internal recombination and global PGL motions. The 11 BILR cubes satisfy the three moments over $\mathbb Z$: traces $7$ at $+1$ and $4$ at $-1$, active form span rank 8, $K=\sum w_i\mu_i\mu_i^T$, $\sum w_i\mu_i=0$, $\sum w_i=3$. The exact cubic residual identity is also verified. Deleting any one fixed BILR cube violates the moment equations; this is a control for the fixed nodes, not an exclusion of moved ten-node configurations. The nonzero `12 x 12` minor determinant for `Phi` is `-1`.

**Scope.** The $m\le4$ conclusion is conditional on $\ker\Psi=0$ / traceless free orbits; for three-dimensional planes this can be checked by $\ker\Phi=0$. Internal-recombination and global-conjugation samples do not test other exterior components. Pairwise absence of shared 2-planes is not enough by itself to prove $\Phi$ injective. For $m\ge5$, nonzero trace branches remain open: in independent orbit coordinates a single orbit's $q_j$ has rank $0,2,$ or $3$ (never $1$), but after pullback to a degenerate span its rank may drop to 1; dependent traceless parts can add zero exterior volume while leaving nonzero trace parameters. The full $s^2$ and $s^3$ equations must be included.

### 2. Characteristic-zero aligned inner/sandwich termwise exclusions

**Statement.** In characteristic zero, a noncentral Lie-algebra inner/sandwich stabilizer element cannot act termwise projectively on a length-`<=22` full-span decomposition of `T_333`. Nonsemisimple termwise alignment forces too few independent eigenvectors; semisimple repeated-difference weight patterns decompose into blocks whose protected small-format rank lower bounds sum to at least 23.

**Evidence/proof carriers.** [terracini_jordan_synthesis.md](../../deformation_and_incidence/notes/terracini_jordan_synthesis.md), [nonsemisimple_alignment_lemma.md](../../deformation_and_incidence/notes/nonsemisimple_alignment_lemma.md), [semisimple_arrangement_classification.md](../../deformation_and_incidence/notes/semisimple_arrangement_classification.md), [blaser_bound_and_nontransverse_exclusion.md](../../deformation_and_incidence/notes/blaser_bound_and_nontransverse_exclusion.md), `workspace/data/semisimple_arrangement/`, [blaser_closure_and_symmetry.md](../../deformation_and_incidence/notes/blaser_closure_and_symmetry.md).

**Load-bearing inputs.** The needed rectangular input is supported through CHL's result `\underline R(M_{<2,3,3>})=14` and factor-cyclic equivalence, not through an unretrieved Blaser ordinary-rank text.

**Scope.** Covers termwise-aligned inner/sandwich strata only. It does not cover cyclic outer rotation, transpose-containing elements, orbit-permuting decompositions, or general transverse incidence.

### 3. Characteristic-zero finite-order inner/sandwich termwise exclusions

**Statement.** In characteristic zero, a noncentral finite-order inner/sandwich element cannot fix every summand projectively in a length-`<=22` decomposition. The repaired argument refines multiplicative blocks by additive weights and uses only protected low-dimensional direct-sum/additivity mechanisms and slice substitutions.

**Evidence/proof carriers.** [corrected_multiplicative_transfer.md](corrected_multiplicative_transfer.md), [torsion_layer_repair.md](../../symmetry_and_residuals/notes/torsion_layer_repair.md), `workspace/data/semisimple_arrangement/`.

**Scope.** Narrow termwise-fixed statement only. It must not be generalized using unrestricted tensor direct-sum additivity; that earlier route was invalid.

### 4. Pure cyclic characteristic-zero `m <= 3` exclusion

**Statement.** A characteristic-zero pure cyclic rank-22 decomposition has skeleton `f+3m=22`. Modulo symmetric cubic terms, the free cyclic orbit part projects to the Cartan trivector
\[
\omega(X,Y,Z)=\operatorname{tr}(X[Y,Z])\in\Lambda^3(\mathfrak{sl}_3).
\]
The `GL_8` orbit of `omega` is open in `\Lambda^3(C^8)`, while `\sigma_3(G(3,8))` has dimension at most 48, strictly smaller than 56. Therefore `omega` is not a sum of at most three decomposable trivectors, excluding pure cyclic skeletons `(22,0),(19,1),(16,2),(13,3)` in characteristic zero.

**Evidence/proof carriers.** [sl3_trivector.py](../code/sl3_trivector.py), [sl3_trivector_verification.json](../results/sl3_trivector/sl3_trivector_verification.json), [prehomogeneity_and_cyclic_feasibility.md](../../symmetry_and_residuals/notes/prehomogeneity_and_cyclic_feasibility.md), [cyclic_algebraic_refinement.md](../../symmetry_and_residuals/notes/cyclic_algebraic_refinement.md).

**Scope.** Pure cyclic only; the remaining pure cyclic cases `(10,4),(7,5),(4,6),(1,7)` are not closed.

### 5. Exact BILR residual Waring rank 11

**Statement.** The reconstructed BILR `Z4 x Z3` rank-23 scheme has 11 cubes plus four cyclic 3-orbits. For the fixed BILR residual cubic (after subtracting the four free cyclic orbits), the Koszul--Young flattening `Lambda^4 V \otimes V^* -> Lambda^5 V \otimes V` has rank 722 over several good primes. A single cube contributes rank at most 70, so no ten-cube expression exists for this residual. Since the displayed BILR residual is an eleven-cube expression, its Waring and border-Waring rank are exactly 11.

**Evidence/proof carriers.** [ballard_z4_cyclic_scheme.py](../../exact_baselines/code/ballard_z4_cyclic_scheme.py), [ballard_z4_cyclic_scheme.json](../../exact_baselines/results/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json), [ballard_cyclic_analysis_v2.json](../../symmetry_and_residuals/results/ballard_z4_cyclic/ballard_cyclic_analysis_v2.json), [ballard_delete_linearization_v2_merged.json](../../symmetry_and_residuals/results/ballard_z4_cyclic/ballard_delete_linearization_v2_merged.json), [cyclic_algebraic_refinement.md](../../symmetry_and_residuals/notes/cyclic_algebraic_refinement.md).

**Scope.** The exact rank-11 Waring statement is for the fixed BILR residual cubic, not for all residuals over the rank-4 exterior fiber. The one-cube deletion first-order barrier is local to the BILR chart.

### 5b. Hessian commutator certificate for the fixed BILR residual (earlier analysis)

**Statement (Strassen-type commutator bound, symmetric cubic specialization).** Let $R$ be a cubic form in $n$ variables over a field of characteristic $\ne2,3$ with $K=(1/6)\operatorname{Hess}_R(p)$ invertible at a point $p$. Define $H_X=K^{-1}S_X$ with $S_X=(1/6)\operatorname{Hess}_R(X)$. Then $H_p=I$, each $H_X$ is $K$-self-adjoint, and $C=[H_X,H_Y]$ satisfies $KC+C^TK=0$, so $\operatorname{rank}(C)$ is even and all odd traces vanish (in particular $\operatorname{tr}(C^3)=0$ automatically). If $R=\sum_{i=1}^k\rho_i\ell_i^3$ is any Waring decomposition, then
$$\operatorname{rank}([H_X,H_Y])\le2\max(0,k-n)\quad\text{for all }X,Y.$$
Proof: with $A$ the coefficient matrix, $K=ADA^T$, $S_X=AD_XA^T$, and $N=D^{-1}-A^TK^{-1}A$ of rank $k-n$, the commutator middle matrix is $-(D_XND_Y-D_YND_X)$. For $n=9$ and $k\le10$ this gives $\operatorname{rank}\le2$.

**Attribution note.** This is the symmetric-cubic specialization of Strassen's commutator lower bound, not principally a Jennrich result; Jennrich concerns the $k=n$ simultaneous-diagonalization case.

**BILR Pfaffian certificate.** The fixed BILR 11-cube residual on $\mathfrak{gl}_3$ violates the $k\le10$ commutator bound. Define the scalar $\Phi(C):=2\operatorname{tr}(C^4)-\operatorname{tr}(C^2)^2=-8e_4(C)$. Then $\operatorname{rank}(C)\le2\Rightarrow\Phi(C)=0$ always, hence $\Phi(C)\ne0\Rightarrow\operatorname{rank}(C)\ge4$. The converse $\Phi=0\Rightarrow\operatorname{rank}\le2$ holds only when $K$ is positive definite; the trace form on $\mathfrak{gl}_3(\mathbb R)$ has signature $(6,3)$, so $\Phi$ is a one-directional certificate here.

At integer directions $X_1=[3,0,1,3,-1,1,1,3,-2]$, $X_2=[-1,3,-1,-1,1,0,-1,2,1]$:
- For $C=[6S_{X_1},6S_{X_2}]=36[S_{X_1},S_{X_2}]$: $\Phi=-134{,}369{,}280{,}000=-2^{15}\cdot3^8\cdot5^4$.
- True Pfaffian: $\Phi([S_{X_1},S_{X_2}])=-80{,}000=-2^7\cdot5^4$.
- $\operatorname{rank}(C)=4$ mod 65521, 100003, 32003 (matching the bound $2(11-9)=4$).
- $\operatorname{tr}(C^2)=-393{,}984$, $\operatorname{tr}(C^3)=0$, $\operatorname{tr}(C^4)=10{,}427{,}056{,}128$.
- True commutator: $\operatorname{tr}=-304$, $\operatorname{tr}(C^4)=6208$.
- Consistent with analysis's $H2=2H$ quartic $-20{,}480{,}000$ via $C_{\rm raw}=9C_{50}$, $\Phi_{\rm raw}=9^4\Phi_{50}$.

**Span-dimension caution.** In the all-nonzero-weight $k=n+1=10$ normal form the commutator span is $\Lambda^2(U)$ of dimension $\binom d2\in\{0,1,3,6,10,\dots\}$. analysis measured span dimension $4$ at BILR, which obstructs that normal form. However, if a hypothetical 10-cube decomposition has one summand with $\ell_i(p)=0$, a common-factor span can have dimension $4$. Thus span dimension is useful structure but not an unconditional independent proof; the unconditional fixed-BILR lower bound comes from actual rank-4/Pfaffian/common-pencil certificates and the Koszul--Young flattening.

**Frame scan (heuristic only).** 1000 random $SL_3^4$ internal frame changes over $\mathbb F_{65521}$ gave 0 zeros of $\Phi$ at the certificate directions; 500 trials with 9 direction pairs gave 0 common zeros. Schwartz--Zippel with total degree $D\lesssim96$ bounds the hit probability by $D/p$, so a codimension-one zero locus would expect $\lesssim1.5$ hits in 1000 trials. The scan therefore cannot distinguish an empty zero set from a thin proper subvariety; exact elimination is required.

Consistent with the earlier $3\times3$ minor certificate (det $27993600=2^9\cdot3^7\cdot5^2$) and the analysis quartic identity $(-20{,}480{,}000=-2^{15}\cdot5^4)$ via the scaling $36^4/9^4=36^4/6561$. This gives an exact low-degree commutator proof, alongside the Koszul--Young flattening in result 5, that the displayed BILR residual has Waring rank exactly 11.

**analysis support corrections.** A finite-field frame scan is retained only as a warning/calibration: it samples an algebraic locus and cannot exclude the special frame set where a cyclic rank-22 point would live. A one-pair scalar $\Phi$ cannot be used to prove emptiness on $SL_3^4$; the exact rank-2 equations are the $4\times4$ Pfaffians of $\Omega=K[H_X,H_Y]$, and the $k=n+1$ normal form gives stronger common-pencil equations $\Omega(X,Y)\wedge\Omega(X,Z)=0$. analysis calibrated the proposed reduced split equations on BILR: for all six pairs $\{i,j\}|\{k,l\}$, $(P_i+P_j)^\perp\cap\mathfrak{sl}_3$ is two-dimensional and kills the intended corrections, but the full reduced commutator has rank 0 at the BILR identity (the Jordan-only part has rank 4 and is exactly canceled). Therefore that cheap two-frame elimination is inactive on the BILR frame.

**Additional exact certificate.** analysis produced a common-pencil certificate for the fixed BILR residual: with the same $X,Y$ as above and $Z=\operatorname{diag}(1,-1,0)$, $\Omega(X,Y)\wedge\Omega(X,Z)$ has 9 nonzero $\Lambda^4(\mathfrak{sl}_3)$ coefficients, first coefficient $-19440$, while $\operatorname{rank}\Omega(X,Y)=4$ and $\operatorname{rank}\Omega(X,Z)=2$. This violates the $k=n+1$ common-vector normal form. Since $\Omega(X,Y)$ already has rank 4, this is a second reading of the same Strassen--Hessian equation system rather than a fully independent lower-bound mechanism.

**Evidence/proof carriers.** [pfaffian_certificate.py](../../symmetry_and_residuals/code/pfaffian_certificate.py), [pfaffian_certificate_and_scan.json](../../symmetry_and_residuals/results/pfaffian_certificate/pfaffian_certificate_and_scan.json), [associator_lemma_and_certificate.md](../../symmetry_and_residuals/notes/associator_lemma_and_certificate.md), [reduced_pair_associator_calibration.py](../../symmetry_and_residuals/code/reduced_pair_associator_calibration.py), [bilr_reduced_pair_calibration.json](../../symmetry_and_residuals/results/reduced_pair_associator/bilr_reduced_pair_calibration.json), [common_pencil_certificate.py](../../relaxations_and_cuts/code/common_pencil_certificate.py), [bilr_common_pencil_certificate.json](../../symmetry_and_residuals/results/reduced_pair_associator/bilr_common_pencil_certificate.json), plus earlier: [jennrich_integer_cert.py](../../symmetry_and_residuals/code/jennrich_integer_cert.py), [jennrich_integer_certificate.json](../../symmetry_and_residuals/results/hessian_commutator/jennrich_integer_certificate.json), [jennrich_corrected_scope.md](../../symmetry_and_residuals/notes/jennrich_corrected_scope.md).

**Scope.** This result is for the fixed BILR residual cubic. It does not prove a universal pure-cyclic `(10,4)` exclusion, because an exterior decomposition of the Cartan trivector does not determine the symmetric residual cubic: determinant-one frame changes inside each exterior plane preserve $u_j\wedge v_j\wedge w_j$ but change $u_jv_jw_j$. A cyclic rank-22 point, if it exists in the `(10,4)` traceless branch, must lie in the closed locus where all $4\times4$ Pfaffians of $\Omega$ and all common-pencil equations vanish for every relevant $(X,Y,Z)$; nonvanishing at BILR gives no exclusion of that locus. The current use of the commutator bound is therefore as an exact residual test and as a double-edged candidate/exclusion instrument for the unresolved `(10,4)` branch, not as a completed branch proof.

### 6. `F_2` named-family certificates

**Order-7 diagonal sandwich family.** The corrected order-7 diagonal projector certificate excludes `F_2` rank-`<=22` `UV`-span representations whose rank-one terms are permuted by the specified order-7 subgroup. Carrier: [order7_family_certificate_v2.json](../../symmetry_and_residuals/results/order7_exhaustive/order7_family_certificate_v2.json).

**Pure cyclic diagonal-collapse skeletons.** Exact diagonal specialization with replayed DRAT proofs excludes pure cyclic `F_2` skeletons `(22,0),(19,1),(16,2),(13,3)`. Carriers: [diagonal_collapse_results.json](../results/diagonal_collapse/diagonal_collapse_results.json), [cyclic_diagonal_collapse_and_outer_status.md](../../symmetry_and_residuals/notes/cyclic_diagonal_collapse_and_outer_status.md).

**Mixed `Z4` finite-field restricted tests.** The `F_2` mixed `Z4` by cyclic encoders give DRAT-verified exclusions in their stated finite-field symmetry models, with positive controls. Carriers: `workspace/data/z4_cyclic_f2_drat/`, `workspace/data/z4xcyclic_general_f2_drat/`, [z4_mixed_f2_restricted_exclusion.md](../../symmetry_and_residuals/notes/z4_mixed_f2_restricted_exclusion.md).

**Scope.** These are finite-field and named-family results. They do not transfer to characteristic zero or unrestricted decompositions.

### 7. Single-free-orbit `Z4` characteristic-zero local structure and corrected block instrument

**Statement.** At BILR, the single-free-orbit `Z4` exterior equation has tangent kernel dimension 10, generated by eight internal `SL3` recombination directions and two centralizer-conjugation directions. In the canonical Q-basis of analysis, the invariant cubic blocks and orbit-cube structure are now consistently represented.

**Evidence/proof carriers.** [z4_symmetry_kernel_and_residual.json](../../symmetry_and_residuals/results/z4_symmetry_kernel/z4_symmetry_kernel_and_residual.json), [z4_symmetry_kernel_and_residual.md](../../symmetry_and_residuals/notes/z4_symmetry_kernel_and_residual.md), [z4_qbasis_selftest.py](../../symmetry_and_residuals/code/z4_qbasis_selftest.py), [qbasis_selftest.json](../../symmetry_and_residuals/results/z4_qbasis/qbasis_selftest.json), [z4_tail_positive_control.py](../../symmetry_and_residuals/code/z4_tail_positive_control.py), [tail_positive_control_bilr_v2.json](../../symmetry_and_residuals/results/z4_qbasis/tail_positive_control_bilr_v2.json), [z4_qbasis_and_tail_scaling.md](../../symmetry_and_residuals/notes/z4_qbasis_and_tail_scaling.md).

**New analysis rule.** Convert packed forms by `A=L^T`, diagonalize `a0^T` using `Q`, and use `A''=Q^{-1}AQ`, `M''=Q^{-1}MQ`. In this basis the target qz2/qw2 blocks are rank-one hyperbolic blocks with different q-directions. Size-four orbit off blocks determine the orbit only up to hidden tail scaling `z -> t z`, `w -> eps*t w`, `q -> t^{-2}q`, `p -> eps*t^{-2}p`, so the tail multiplier is `h=eps*t^{-6}` and tail equations require separate nonzero scalars `h1,h2`. This symbolic identity is recorded in [symbolic_orbit_formula.json](../../symmetry_and_residuals/results/z4_qbasis/symbolic_orbit_formula.json).

**Scope.** This instrument is not yet a characteristic-zero emptiness proof or a rank-22 construction. It prevents false exclusions by making the generic/proportional/zero-q branch structure and hidden tail scalars explicit.

## Withdrawn arguments that must not be reused

- Numerical continuation or machine-small residuals are border-rank/cancellation signals, not exact rank-22 evidence.
- The early second-order obstruction from individual tangent directions was invalid; only the full Kuranishi projection has its limited formal meaning.
- The E11/Wang occupation and matching-stratum certificates are scoped; withdrawn related analysis rank-21/F2 claims do not establish a global lower bound.
- The unrestricted tensor direct-sum additivity transfer is invalid; use only the repaired protected low-dimensional version.
- Raw `Ad(a0)` residual non-invariance was a coordinate error; the correct packed-pairing action is transpose-dual, now fixed by the Q-basis rule.
- Generic rank-two pencil extraction in the `Z4` block system is incomplete without proportional-q and zero-q branches and without the hidden tail scalars; a `4+4+2` tail test must use both the `6P Q^2` and matching `2P^3` length-two orbit constants.
- analysis's asserted proof that `m_0(L_anti)=9` is false: it restricted arbitrary free transpose-orbit vectors to row-pure/no-noise bivectors and tested Laderman in mismatched `Phi_3 Phi_4` versus standard-`tau` coordinates. analysis transports Laderman correctly and gives an eight-bivector witness, so the derived elimination of `(8,7)` and `(6,8)` must not be used.

1. **Analyze the rank-four exterior fiber of the Cartan trivector.** For pure cyclic `m=4`, every exterior summand is three-dimensional because a dependent summand would leave the Cartan trivector in `\sigma_3(G(3,8))`, contradicting result 4. Thus the tracelessness question is exactly whether `\Phi:\oplus_j\Lambda^2(P_j)\to\Lambda^2(\mathfrak{sl}_3)` is injective on every rank-four exterior decomposition. The BILR determinant `-1` proves this on the BILR `PGL3` orbit; other exterior components, if they exist, must be found or excluded.

2. **Analyze the $\ker\Psi\ne0$ branch for $m\ge5$.** Classify decomposable-bivector relations in $\Lambda^2(\mathfrak{sl}_3)$ for degenerate exterior summands ($w=u+v$, etc.). Impose the full nonzero-trace $s^1,s^2,s^3$ system on skeletons $(7,5),(4,6),(1,7)$. Do not use sampling or the rank-one perturbation heuristic.

3. **Proof consolidation and formal document.** Assemble the exact chain: independent-UV refinement → aligned-strata exclusion → finite-order inner theorem → Cartan $m\ge4$ → trace-grading $f\ge8$ under `\ker\Psi=0` → Strassen commutator proof for the fixed BILR residual → pure cyclic conditional theorem. The Bernardi–Vanzo 3-identifiability result applies to generic points of `\sigma_3(G(3,8))`; it does not settle the special rank-four fiber of the Cartan trivector.

4. **Non-cyclic routes.** The saturated independent-UV incidence remains the global formulation covering arbitrary rank-22 decompositions. The E11/Wang finite-field program (related analysis) provides complementary evidence.

### 8. Draft mathematical note (analysis)

A 4-page draft `workspace/drafts/rank22_structural_constraints.tex` consolidates results 1–5 above into a self-contained mathematical document with proofs (or proof sketches) for: Cartan prehomogeneity (m ≥ 4), trace-graded collapse ((10,4) conditional), Strassen commutator bound with BILR Pfaffian certificate (Waring rank 11), independent-UV reformulation, and termwise-aligned exclusion. Bibliography in `workspace/drafts/refs.bib`. This is a working draft, not a final paper.

### 9. Local KY stratification at the BILR residual (analysis; scope repaired analysis)

**Statement.** At the displayed BILR internal frame, the 1134×1134 Koszul–Young flattening of the residual cubic R has rank 722 (corank 412). Among the 32 internal frame tangent directions (4 planes × 8 sl_3 basis elements), exactly the 8 torus directions (H₁, H₂ per plane, which fix R identically) are tangent to the stratum {KY rank ≤ 722}. All 24 non-torus directions have strictly positive rank(V^T KY(δR) U), verified independently mod 65521 (ranks 26–84) and mod 32003 (ranks 11–70). The ranks are orbit-independent, reflecting the Z₄ symmetry.

**Evidence/proof carriers.** [ky_tangent_at_bilr.py](../../deformation_and_incidence/code/ky_tangent_at_bilr.py), [ky_tangent_at_bilr.json](../../deformation_and_incidence/results/ky_tangent/ky_tangent_at_bilr.json). Second-prime verification inline in analysis.

**Consequence.** KY rank is lower semicontinuous, so because the displayed BILR residual has KY rank 722, a sufficiently small neighborhood of that point already avoids the KY≤700 locus needed for Waring rank ≤10. The analysis calculation sharpens the germ of the higher stratum: the Zariski tangent to {KY≤722} at BILR is exactly the 8-dimensional gauge tangent, so no additional low-KY branch passes infinitesimally through the displayed frame.

**Scope.** This is a local statement about the germ at the displayed BILR internal frame. It does not exclude finite-distance rank-10 strata inside the same frame family, other exterior components, twisted cyclic classes, m≥5 cyclic skeletons, or non-cyclic decompositions.

### 10. Klein V₄ and C₄ regular exterior families are conjugacy-consistent with BILR (analysis)

**Statement.** Over F₅, all 8 tested Klein V₄ exterior-section points and all 8 tested C₄ regular points match the BILR signature: det restricted to each plane ≡ 0 and Killing conic determinant = −2 on all 4 planes. These are PGL₃-invariant properties. Both chart dimensions (2) match dim C_{PGL₃}(H).

**Evidence/proof carriers.** [klein_conjugacy_check.py](../../symmetry_and_residuals/code/klein_conjugacy_check.py), [klein_conjugacy_discriminants.json](../../symmetry_and_residuals/results/klein_conjugacy/klein_conjugacy_discriminants.json).

**Scope.** Consistency with conjugacy, not proof of conjugacy. These invariants cannot detect inequivalent components that happen to share the same det/killing data. Components with trivial stabilizer remain invisible to symmetric ansätze.

### 11. Order-3 cyclic-type twists are adapted-coordinate copies of pure cyclic (analysis)

**Statement.** Let `char K` be neither 2 nor 3 and let `P in GL3(K)` have `P^3` scalar. Put `g=Ad(P)` and
\[
\rho_P(X,Y,Z)=(g^2Y,g^2Z,g^2X).
\]
Then `rho_P^3=1`, `rho_P` preserves `T(X,Y,Z)=tr(XYZ)`, and
\[
Q(X,Y,Z)=(X,gY,g^2Z)
\]
conjugates `rho_P` to the ordinary cyclic rotation `(X,Y,Z) -> (Y,Z,X)`. Hence the order-3 cyclic-type invariant tensor space has the same dimension and orbit structure as the pure cyclic case: coordinate orbit histogram `1:9, 3:240` and dimension `249`. On the fixed locus `(X,gX,g^2X)`,
\[
C_P(X)=\operatorname{tr}(XgXg^2X)=\lambda^{-1}\operatorname{tr}((XP)^3),\qquad P^3=\lambda I.
\]
The full exterior target has radical `K P^{-1}`. On the adapted eight-space
\[
\mathfrak h_P=\{X:\operatorname{tr}(XP)=0\}=\mathfrak{sl}_3 P^{-1},
\]
the projected exterior form is a Cartan-form coordinate image with `GL8` stabilizer dimension `8`; therefore the same dimension comparison with `sigma_3(G(3,8))` gives `m>=4` in adapted coordinates. The adapted trace-grading quadratic in `X=M+sP^{-1}` has rank `8`.

**Evidence/proof carriers.** [twisted_cyclic_action_selfcheck.py](../../symmetry_and_residuals/code/twisted_cyclic_action_selfcheck.py), [twisted_cyclic_action_selfcheck.json](../../symmetry_and_residuals/results/twisted_cyclic/twisted_cyclic_action_selfcheck.json), and review verification `independent-verification-record`. The initial exploratory file [twisted_cyclic_invariants.json](../../symmetry_and_residuals/results/twisted_cyclic/twisted_cyclic_invariants.json) computed useful `C_P`, KY, and exterior data, but its `245/243` invariant-dimension interpretation is superseded for actual order-3 `rho_P` actions.

**Scope.** This repairs the cyclic formulation rather than opening a separate twisted order-3 search branch. The transfer of the trace-grading `f>=8` ARTIFACT still requires the adapted mixed-trace map to force free orbit representatives to vanish on `P^{-1}`. The finite-distance `(10,4)` residual Waring problem, `m>=5` mixed-trace branches, and unrestricted independent-UV incidence remain open.

### 12. Transpose complementary sector, Laderman eight-witness, and corrected Gram status (earlier analysis and 66)

**Statement.** Work over a field of characteristic not 2, with the standard transpose involution \(\tau(u,v,w)=(u^T,w^T,v^T)\) and after identifying the third factor with the transposed second factor. The \(\tau\)-invariant tensor space splits as
\[
(K^9)^{\otimes3}_+\simeq \operatorname{Sym}_3\otimes\operatorname{Sym}^2(K^9)\oplus \Lambda^2K^3\otimes\Lambda^2(K^9),
\]
with dimensions \(270+108=378\). In the complementary sector fixed \(\tau\)-terms vanish and each free two-orbit contributes one structured term \(c\otimes(p\wedge q)\). For the complementary target \(L_{\rm anti}=\langle -\sum_k e_{0k}\wedge e_{1k},-\sum_k e_{0k}\wedge e_{2k},-\sum_k e_{1k}\wedge e_{2k}\rangle\), the minimum number \(m_0\) of decomposable bivectors whose span contains \(L_{\rm anti}\) satisfies the field-independent bound
\[
7\le m_0\le 9.
\]
The lower bound is carried by the exact \(A\)-wedge flattening \(A\otimes W^*\to\Lambda^2A\otimes W\), whose integer determinant is \(8\); each structured free orbit has flattening rank at most \(4\). The original upper bound is the displayed columnwise nine-bivector decomposition.

**analysis sharper upper witness.** Over \(\mathbb C\), \(\mathbb Q(i)\), \(\mathbb F_{65521}\), and the tested odd finite fields \(\mathbb F_3,\mathbb F_5,\mathbb F_7,\mathbb F_{11},\mathbb F_{13}\), transport the Burichenko/Laderman \(\Phi_3\Phi_4\)-invariant rank-23 scheme to standard \(\tau\). A convenient diagonal normalization over fields containing \(\sqrt{-1}\) is
\[
g(A,B,C)=\bigl(PAQ^{-1},\;QBR^{-1},\;RCP^{-1}\bigr),\qquad
P=I,
\quad Q=\epsilon_1\pi_{12}=\pi_{12}\epsilon_2,
\quad R=\operatorname{diag}(i,1,1),
\]
so that \(\tau g=g\Phi_3\Phi_4\). More generally, replacing \(Q\) by \(\delta Q\) and choosing \(R^T R=\delta\epsilon_1\) gives the same transport over the tested odd finite fields, including \(\mathbb F_3\). Exact replay verifies that the transported 23 terms still sum to \(T_{333}\), have standard-\(\tau\) skeleton \((7,8)\), and that the seven fixed terms have zero complementary bivector. The eight free-orbit representative bivectors have rank 8 and contain \(L_{\rm anti}\); over \(\mathbb Q(i)\) the three target rows are expressed by coefficient rows
\[
(1,1,-1,-1,0,0,0,0),\quad
(0,0,1,0,1,1,1,0),\quad
(0,0,-1,-1,-1,0,0,1).
\]
Therefore, over these fields,
\[
7\le m_0\le8.
\]
No seven-subset of this particular Laderman eight-witness contains \(L_{\rm anti}\); this is only a property of that witness, not a proof that \(m_0\ge8\).

**Additional structured consequence.** The literal analysis row-norm polarization split with six fixed squares and six free products cannot be completed to a \((6,8)\) rank-22 \(\tau\)-skeleton by adding only two free orbits: those six free products lie entirely in \(\operatorname{Sym}^2U\otimes\Lambda^2C\), while the complementary target lies in \(\Lambda^2U\otimes\operatorname{Sym}^2C\) with three-dimensional projection. Two further free orbits can supply at most two dimensions in that projection. This does not exclude general \((6,8)\) skeletons with a different Gram realization.

**Evidence/proof carriers.** [transpose_complement_entry.md](../../symmetry_and_residuals/notes/transpose_complement_entry.md), [transpose_complement.py](../../symmetry_and_residuals/code/transpose_complement.py), [transpose_complement_entry.json](../../symmetry_and_residuals/results/transpose_complement/transpose_complement_entry.json), [anti_Awedge_integer.py](../code/anti_Awedge_integer.py), [anti_Awedge_integer_det.json](../../symmetry_and_residuals/results/transpose_component/anti_Awedge_integer_det.json), [component_obstruction.py](../code/component_obstruction.py), [component_obstruction_f6m8_polarization.json](../../symmetry_and_residuals/results/transpose_component/component_obstruction_f6m8_polarization.json), review check `independent-verification-record`; analysis correction and transport: [transported_laderman_tau_correction.md](../../exact_baselines/notes/transported_laderman_tau_correction.md), [transport_laderman_to_standard_tau.py](../../exact_baselines/code/transport_laderman_to_standard_tau.py), [transported_laderman_standard_tau_F65521.json](../../exact_baselines/results/transport_laderman_tau/transported_laderman_standard_tau_F65521.json), [transport_laderman_qi.py](../../exact_baselines/code/transport_laderman_qi.py), [transported_laderman_standard_tau_Qi.json](../../exact_baselines/results/transport_laderman_tau/transported_laderman_standard_tau_Qi.json), [transport_laderman_general_ff.py](../../exact_baselines/code/transport_laderman_general_ff.py), [transported_laderman_general_finite_fields.json](../../exact_baselines/results/transport_laderman_tau/transported_laderman_general_finite_fields.json), [laderman_m7_subsets.py](../../exact_baselines/code/laderman_m7_subsets.py), [transported_laderman_m7_subsets_F65521.json](../../exact_baselines/results/transport_laderman_tau/transported_laderman_m7_subsets_F65521.json), compact certificate [laderman_8bivector_certificate_Qi.json](../../exact_baselines/results/transport_laderman_tau/laderman_8bivector_certificate_Qi.json); fixed-free-span compression tests: [fixed_completion_general_ff.py](../../occupation_and_completion/code/fixed_completion_general_ff.py), [fixed_completion_general_finite_fields.json](../../occupation_and_completion/results/fixed_completion_enum/fixed_completion_general_finite_fields.json), [general_completion_fixed_free.py](../../occupation_and_completion/code/general_completion_fixed_free.py), [general_completion_fixed_free_F3.json](../../occupation_and_completion/results/general_completion/general_completion_fixed_free_F3.json), and Singular output `workspace/data/fixed_completion_enum/fixed_completion_F5_singular_output.txt`.

**Range of use.** This is a symmetry-restricted entry condition for decompositions whose rank-one terms are permuted by the standard \(\tau\). It is not a global rank-22 exclusion. analysis's assertion \(N_G=12\) for the Gram sector is superseded: the current Gram result is only an upper-bound construction in the domains where its polarization constants are realized; no Gram lower bound excluding \((0,11)\) has been proved. analysis's asserted proof of \(m_0=9\), and the derived removal of \((8,7)\) and \((6,8)\), are withdrawn. The presently unresolved standard-\(\tau\) rank-22 skeletons over algebraically closed characteristic zero are \((8,7),(6,8),(4,9),(2,10),(0,11)\), subject to the full corrected containment, not merely the complementary sector.

### 13. Two-sector decomposition, frozen-span theorem, and f-parity (analysis)

**Two-sector decomposition.** Under standard \(\tau\) in characteristic \(\ne2\), the first slice space decomposes as \(L_1=L_{\mathrm{sym}}(6)\oplus L_{\mathrm{anti}}(3)\). The containment condition for a \(\tau\)-stable decomposition with skeleton \((f,m)\) is:
\[
L_{\mathrm{anti}}\subseteq\operatorname{span}\{v_j\wedge w_j\},
\qquad
L_{\mathrm{sym}}\subseteq\operatorname{span}\{x_ix_i^T\}+\operatorname{span}\{v_j\odot w_j\},
\]
where the first condition involves only the \(m\) free pairs and the second couples \(f\) fixed terms to \(m\) free symmetric products. All five surviving rank-22 skeletons have 198 unknowns \((=9\cdot22)\) before symmetry reduction. Verified modular over \(\mathbb F_{65521}\) with the transported Laderman scheme.

**Frozen-Laderman-free-span theorem.** Over \(\mathbb Q(i)\), the compatibility variety for \(\tau\)-fixed rank-one generators in \(F+L_1\) (59 quadrics in \(\mathbb P^8\)) has projective dimension 0 and degree 3, with exactly three \(\mathbb Q(i)\)-rational points in charts \(x_2,x_5,x_8\). The same degree 3 holds over \(\mathbb F_5\) (analysis). Since a \((6,8)\) completion requires 6 generators spanning a 6-dimensional quotient and only 3 exist, no \(\tau\)-rank-22 scheme shares the transported Laderman eight free orbits, over any field containing \(\mathbb Q(i)\). For general rank-one generators (bilinear ideal, 59 equations in \(\mathbb P^{17}\)), the variety has projective dimension 8 and degree 2; over \(\mathbb F_3\), its quotient images still span only 3 dimensions (analysis).

**f-parity invariant.** Free-free orbit flips and free-orbit reductions preserve \(f\bmod 2\); since \(r=f+2m\), rank parity equals \(f\) parity. The standard seed has \(f=9\) (odd) and the transported Laderman has \(f=7\) (odd), so the currently implemented walk can reach only odd ranks. Rank 22 requires parity-changing moves: orbit collapse, fixed-term addition, or fixed-term removal.

**Corrected Laderman/free-span structure.** At the transported witness, the eight free symmetric products \(v_j\odot w_j\) lie entirely in \(F\); in fact this is true for every free orbit by definition, so they never contribute nonzero quotient modulo the full free span. The useful invariant is \(s(F)=\dim(F\cap L_{\mathrm{sym}})\), with \(q(F)=\dim((F+L_1)/F)=6-s(F)\) once \(L_{\mathrm{anti}}\subset F\). Laderman has \(s(F)=0\), \(q(F)=6\), and its compatible fixed-square variety has only three quotient directions; direct deletion of any fixed term breaks containment. For (6,8), the free span must move so that \(Z(F)=\{[x]:xP(x)^T\in F+L_1\}\) has six independent quotient directions, not so that a free symmetric product has a nonzero quotient. For (4,9),(2,10),(0,11), the required special loci have \(s(F)\ge2,4,6\), respectively, together with the fixed-square quotient condition.

**Evidence carriers.** [two_sector_Qi_compat.py](../../symmetry_and_residuals/code/two_sector_Qi_compat.py), [decisive_containment.py](../code/decisive_containment.py), [compatibility_Qi.sing](../../symmetry_and_residuals/code/two_sector/compatibility_Qi.sing), [two_sector_results.json](../../symmetry_and_residuals/results/two_sector/two_sector_results.json), [decisive_containment.json](../../symmetry_and_residuals/results/two_sector/decisive_containment.json), [two_sector_synthesis.md](../../symmetry_and_residuals/notes/two_sector_synthesis.md).
