# Individual Plane Orbit Certificates

This private extension concerns only report representatives 484--491. It does
not change the main lower-bound theorem or introduce a classification premise.
It does not prove the complete fourteen-orbit classification, the 43,435-plane
total, the 32,018 all-high total, or the six-bases-per-plane formula.

## Mathematical Boundary

`QiushiMatmul.PlaneOrbit.Equivalent W V` is the equivalence closure of
`ActionStep`: either there are matrices `P`, `Q` with unit determinants and
`actionW P Q W = V`, or `transposeW W = V`.

Here `actionW` is the existing semantic action induced by
`A -> P^T A Q^(-T)`. No matrix rank signature or
producer-supplied orbit label defines this relation.

The separate `QiushiPlaneOrbitSizes` module exposes these statements:

```lean
exact_orbit_sizes (i : Fin 8) :
  Nat.card {W : Submodule F2 Mat3 // Equivalent (ahPlaneW i) W}
    = reportedSize i

representatives_inequivalent (i j : Fin 8) (hij : Not (i = j)) :
  Not (Equivalent (ahPlaneW i) (ahPlaneW j))

orbit_member_dimension (i : Fin 8) (W : Submodule F2 Mat3)
  (h : Equivalent (ahPlaneW i) W) : Module.finrank F2 W = 2
```

`reportedSize` is `[98, 2352, 1176, 3528, 14112, 4704, 4704, 1344]`, in
certificate order 484--491. `no_invertible_transport` rules out a single
invertible action, with or without a preceding transpose, between distinct
representatives. `represented_orbit_count` counts exactly the eight quotient
classes represented by this list, not the classes of all two-dimensional
subspaces. None of these statements takes `FinitePremises` or a numerical
counting hypothesis.

## Proof Architecture

1. `QiushiPlaneOrbitCode` decodes canonical pairs into actual spans. It proves
   dimension two and injectivity by matrix-code round trips and F2 span
   membership. It does not count bases.
2. `QiushiPlaneOrbitGenerators` checks four code actions against linear maps:
   row swaps 0/1 and 1/2, row transvection 0 <- 0+1, and transpose.
3. `QiushiPlaneOrbitGL` checks a row-generator word for every nonsingular
   matrix code. `invertible_word` uses the existing matrix-code round trip to
   quantify over every actual invertible matrix, not just the produced list.
4. `QiushiPlaneOrbitAction` proves that closure under those four generators
   implies invariance under the full invertible `actionW` and transpose.
   Transpose supplies right actions from left actions; inverse actions handle
   symmetry of the equivalence relation.
5. `QiushiPlaneOrbitCertificate` proves a reusable theorem for finite tables.
   Adjacent strict ordering proves injective decoding. Decreasing parent
   depths prove connectivity to the root. Four checked outgoing images prove
   closure. The table is consequently in bijection with the semantic orbit.
6. Distinct minimum canonical root keys prove inequivalence. This separates
   489 and 490 even though both have size 4,704.

The producer is untrusted. Its data contain one canonical pair per orbit
member, parent depths and four graph edges. Literal lookup arrays and checks
are split into 128-row pieces to keep kernel reduction bounded. Shards use
`decide +kernel +revert`, never native evaluation or skipped kernel checking.

## Private Replay

Supply the parent clean build's `environment.json` explicitly:

```sh
python3 tools/generate_finite_orbits.py
python3 tools/build_finite_orbits.py --environment "$CLEAN_ENVIRONMENT" --all --jobs 2
python3 -m unittest discover -s tests -p test_finite_orbits.py -v
```

The builder uses only the supplied clean library/package search path plus
this worktree's private output directory. It never invokes Lake or writes
parent objects. Outputs and per-module logs are under
`.local/finite-orbits/`; `last-build.json` records source hashes, environment
hash, return codes and timings. `--jobs` accepts only one or two compilers.

`QiushiPlaneOrbitTests` checks a report-plane alias, the equal-size inequivalent
pair, and rejection of invalid certificates, then prints public types and
axiom dependencies. All 277 modules passed kernel checking against clean build
`build-20260914-125249` on 2026-09-14. The full data replay and the final API/test
replays are recorded privately in `eight-kernel-replay.json`,
`eight-api-replay.json`, and `eight-tests-replay.json`; the latter replays fix
only elaboration in the public wrapper and the report-alias test.

The printed dependencies of `genCode_semantics`, `invertible_word`,
`OrbitData.orbit_exact`, `exact_orbit_sizes`, `representatives_inequivalent`,
and `represented_orbit_count` are exactly `propext`, `Classical.choice`, and
`Quot.sound`. There are no remaining eight-orbit semantic obligations. These
are independent report theorems, not additions to the main theorem's premises.
