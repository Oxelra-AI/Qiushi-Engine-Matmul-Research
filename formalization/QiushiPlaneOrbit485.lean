import QiushiPlaneOrbit485Check0
import QiushiPlaneOrbit485Check1
import QiushiPlaneOrbit485Check2
import QiushiPlaneOrbit485Check3
import QiushiPlaneOrbit485Check4
import QiushiPlaneOrbit485Check5
import QiushiPlaneOrbit485Check6
import QiushiPlaneOrbit485Check7
import QiushiPlaneOrbit485Check8
import QiushiPlaneOrbit485Check9
import QiushiPlaneOrbit485Check10
import QiushiPlaneOrbit485Check11
import QiushiPlaneOrbit485Check12
import QiushiPlaneOrbit485Check13
import QiushiPlaneOrbit485Check14
import QiushiPlaneOrbit485Check15
import QiushiPlaneOrbit485Check16
import QiushiPlaneOrbit485Check17
import QiushiPlaneOrbit485Check18

namespace QiushiMatmul.PlaneOrbit.Orbit485

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
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 2352 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit485
