import QiushiPlaneOrbit491Check0
import QiushiPlaneOrbit491Check1
import QiushiPlaneOrbit491Check2
import QiushiPlaneOrbit491Check3
import QiushiPlaneOrbit491Check4
import QiushiPlaneOrbit491Check5
import QiushiPlaneOrbit491Check6
import QiushiPlaneOrbit491Check7
import QiushiPlaneOrbit491Check8
import QiushiPlaneOrbit491Check9
import QiushiPlaneOrbit491Check10

namespace QiushiMatmul.PlaneOrbit.Orbit491

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
  · exact checked10


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 1344 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit491
