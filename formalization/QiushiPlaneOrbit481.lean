import QiushiPlaneOrbit481Check0
import QiushiPlaneOrbit481Check1
import QiushiPlaneOrbit481Check2
import QiushiPlaneOrbit481Check3
import QiushiPlaneOrbit481Check4
import QiushiPlaneOrbit481Check5
import QiushiPlaneOrbit481Check6
import QiushiPlaneOrbit481Check7
import QiushiPlaneOrbit481Check8
import QiushiPlaneOrbit481Check9
import QiushiPlaneOrbit481Check10
import QiushiPlaneOrbit481Check11
import QiushiPlaneOrbit481Check12
import QiushiPlaneOrbit481Check13
import QiushiPlaneOrbit481Check14
import QiushiPlaneOrbit481Check15
import QiushiPlaneOrbit481Check16
import QiushiPlaneOrbit481Check17
import QiushiPlaneOrbit481Check18
import QiushiPlaneOrbit481Check19
import QiushiPlaneOrbit481Check20
import QiushiPlaneOrbit481Check21
import QiushiPlaneOrbit481Check22
import QiushiPlaneOrbit481Check23
import QiushiPlaneOrbit481Check24
import QiushiPlaneOrbit481Check25
import QiushiPlaneOrbit481Check26
import QiushiPlaneOrbit481Check27

namespace QiushiMatmul.PlaneOrbit.Orbit481

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
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 3528 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit481
