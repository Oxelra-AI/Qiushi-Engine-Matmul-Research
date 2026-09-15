import QiushiFullTrilinearSymmetry

open Matrix BigOperators
open QiushiMatmul QiushiMatmul.FullTrilinearSymmetry

example (U V H A B C : Mat3) [Invertible U] [Invertible V] [Invertible H] :
    (U.transpose * A * V.transpose⁻¹) * (V.transpose * B * H.transpose⁻¹) *
      (U⁻¹ * C * H).transpose =
        U.transpose * (A * B * C.transpose) * (U⁻¹).transpose :=
  FullTrilinearSymmetry.transformed_product U V H A B C

example (U V H A B C : Mat3) [Invertible U] [Invertible V] [Invertible H] :
    Matrix.trace ((U.transpose * A * V.transpose⁻¹) *
      (V.transpose * B * H.transpose⁻¹) * (U⁻¹ * C * H).transpose) =
        Matrix.trace (A * B * C.transpose) :=
  FullTrilinearSymmetry.trilinear_action U V H A B C

example (U V H X Y Z : Mat3) [Invertible U] [Invertible V] [Invertible H] :
    Matrix.trace ((U * X * V⁻¹) * (V * Y * H⁻¹) *
      (U.transpose⁻¹ * Z * H.transpose).transpose) =
        Matrix.trace (X * Y * Z.transpose) :=
  input_trilinear_action U V H X Y Z

example (U V H A B C X Y Z : Mat3)
    [Invertible U] [Invertible V] [Invertible H] :
    coordinatePairing (U.transpose * A * V.transpose⁻¹) X =
        coordinatePairing A (U * X * V⁻¹) ∧
    coordinatePairing (V.transpose * B * H.transpose⁻¹) Y =
        coordinatePairing B (V * Y * H⁻¹) ∧
    coordinatePairing (U⁻¹ * C * H) Z =
        coordinatePairing C (U.transpose⁻¹ * Z * H.transpose) :=
  coefficient_pairing_pullback U V H A B C X Y Z

example (X Y Z : Mat3) :
    (∑ c : Coord9, (∑ a : Coord9, ∑ b : Coord9,
      X a.1 a.2 * Y b.1 b.2 * tensorEntry a b c) * Z c.1 c.2) =
        Matrix.trace (X * Y * Z.transpose) := tensorEntry_trace X Y Z

example (A X : Mat3) :
    (∑ a : Coord9, A a.1 a.2 * X a.1 a.2) = Matrix.trace (A * X.transpose) :=
  coordinatePairing_eq_trace A X

run_cmd do
  for name in #[``coordinatePairing_eq_trace, ``tensorEntry_trace,
      ``FullTrilinearSymmetry.transformed_product, ``FullTrilinearSymmetry.trilinear_action,
      ``input_trilinear_action, ``pairing_sandwich, ``coefficient_pairing_pullback] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"FULL_TRILINEAR_AXIOMS {name}: {axioms}"
