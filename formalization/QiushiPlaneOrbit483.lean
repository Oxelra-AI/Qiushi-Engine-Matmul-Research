import QiushiPlaneOrbit483Check0
import QiushiPlaneOrbit483Check1
import QiushiPlaneOrbit483Check2
import QiushiPlaneOrbit483Check3
import QiushiPlaneOrbit483Check4
import QiushiPlaneOrbit483Check5
import QiushiPlaneOrbit483Check6
import QiushiPlaneOrbit483Check7
import QiushiPlaneOrbit483Check8
import QiushiPlaneOrbit483Check9
import QiushiPlaneOrbit483Check10
import QiushiPlaneOrbit483Check11
import QiushiPlaneOrbit483Check12
import QiushiPlaneOrbit483Check13
import QiushiPlaneOrbit483Check14
import QiushiPlaneOrbit483Check15
import QiushiPlaneOrbit483Check16
import QiushiPlaneOrbit483Check17
import QiushiPlaneOrbit483Check18
import QiushiPlaneOrbit483Check19
import QiushiPlaneOrbit483Check20
import QiushiPlaneOrbit483Check21
import QiushiPlaneOrbit483Check22
import QiushiPlaneOrbit483Check23
import QiushiPlaneOrbit483Check24
import QiushiPlaneOrbit483Check25
import QiushiPlaneOrbit483Check26
import QiushiPlaneOrbit483Check27
import QiushiPlaneOrbit483Check28
import QiushiPlaneOrbit483Check29
import QiushiPlaneOrbit483Check30
import QiushiPlaneOrbit483Check31
import QiushiPlaneOrbit483Check32
import QiushiPlaneOrbit483Check33
import QiushiPlaneOrbit483Check34
import QiushiPlaneOrbit483Check35
import QiushiPlaneOrbit483Check36

namespace QiushiMatmul.PlaneOrbit.Orbit483

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
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36


theorem size : Nat.card {W : Space // Equivalent (data.space 0) W} = 4704 :=
  data.orbit_card checked

end QiushiMatmul.PlaneOrbit.Orbit483
