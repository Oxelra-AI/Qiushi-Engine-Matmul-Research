import QiushiPlaneOrbit486Check0
import QiushiPlaneOrbit486Check1
import QiushiPlaneOrbit486Check2
import QiushiPlaneOrbit486Check3
import QiushiPlaneOrbit486Check4
import QiushiPlaneOrbit486Check5
import QiushiPlaneOrbit486Check6
import QiushiPlaneOrbit486Check7
import QiushiPlaneOrbit486Check8
import QiushiPlaneOrbit486Check9

namespace QiushiMatmul.PlaneOrbit.Orbit486

theorem checked : ∀ i, data.RowOK i := by
  apply OrbitData.of_blocks (k := 128)
  intro b
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 1176 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit486
