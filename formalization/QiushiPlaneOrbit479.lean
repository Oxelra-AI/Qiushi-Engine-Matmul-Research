import QiushiPlaneOrbit479Check0
import QiushiPlaneOrbit479Check1
import QiushiPlaneOrbit479Check2
import QiushiPlaneOrbit479Check3

namespace QiushiMatmul.PlaneOrbit.Orbit479

theorem checked : ∀ i, data.RowOK i := by
  apply OrbitData.of_blocks (k := 128)
  intro b
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 441 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit479
