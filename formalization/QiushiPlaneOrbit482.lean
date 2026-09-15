import QiushiPlaneOrbit482Check0
import QiushiPlaneOrbit482Check1
import QiushiPlaneOrbit482Check2
import QiushiPlaneOrbit482Check3
import QiushiPlaneOrbit482Check4
import QiushiPlaneOrbit482Check5
import QiushiPlaneOrbit482Check6
import QiushiPlaneOrbit482Check7
import QiushiPlaneOrbit482Check8
import QiushiPlaneOrbit482Check9
import QiushiPlaneOrbit482Check10
import QiushiPlaneOrbit482Check11
import QiushiPlaneOrbit482Check12
import QiushiPlaneOrbit482Check13

namespace QiushiMatmul.PlaneOrbit.Orbit482

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
  · exact checked11
  · exact checked12
  · exact checked13


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 1764 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit482
