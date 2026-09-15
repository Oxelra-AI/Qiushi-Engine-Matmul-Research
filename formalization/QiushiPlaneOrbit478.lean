import QiushiPlaneOrbit478Check0

namespace QiushiMatmul.PlaneOrbit.Orbit478

theorem checked : ∀ i, data.RowOK i := by
  apply OrbitData.of_blocks (k := 128)
  intro b
  fin_cases b
  · exact checked0


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 98 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit478
