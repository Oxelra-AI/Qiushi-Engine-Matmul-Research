import QiushiPlaneOrbit480Check0
import QiushiPlaneOrbit480Check1
import QiushiPlaneOrbit480Check2
import QiushiPlaneOrbit480Check3
import QiushiPlaneOrbit480Check4
import QiushiPlaneOrbit480Check5
import QiushiPlaneOrbit480Check6

namespace QiushiMatmul.PlaneOrbit.Orbit480

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


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 882 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit480
