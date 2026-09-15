import QiushiPlaneOrbit489Check0
import QiushiPlaneOrbit489Check1
import QiushiPlaneOrbit489Check2
import QiushiPlaneOrbit489Check3
import QiushiPlaneOrbit489Check4
import QiushiPlaneOrbit489Check5
import QiushiPlaneOrbit489Check6
import QiushiPlaneOrbit489Check7
import QiushiPlaneOrbit489Check8
import QiushiPlaneOrbit489Check9
import QiushiPlaneOrbit489Check10
import QiushiPlaneOrbit489Check11
import QiushiPlaneOrbit489Check12
import QiushiPlaneOrbit489Check13
import QiushiPlaneOrbit489Check14
import QiushiPlaneOrbit489Check15
import QiushiPlaneOrbit489Check16
import QiushiPlaneOrbit489Check17
import QiushiPlaneOrbit489Check18
import QiushiPlaneOrbit489Check19
import QiushiPlaneOrbit489Check20
import QiushiPlaneOrbit489Check21
import QiushiPlaneOrbit489Check22
import QiushiPlaneOrbit489Check23
import QiushiPlaneOrbit489Check24
import QiushiPlaneOrbit489Check25
import QiushiPlaneOrbit489Check26
import QiushiPlaneOrbit489Check27
import QiushiPlaneOrbit489Check28
import QiushiPlaneOrbit489Check29
import QiushiPlaneOrbit489Check30
import QiushiPlaneOrbit489Check31
import QiushiPlaneOrbit489Check32
import QiushiPlaneOrbit489Check33
import QiushiPlaneOrbit489Check34
import QiushiPlaneOrbit489Check35
import QiushiPlaneOrbit489Check36

namespace QiushiMatmul.PlaneOrbit.Orbit489

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

end QiushiMatmul.PlaneOrbit.Orbit489
