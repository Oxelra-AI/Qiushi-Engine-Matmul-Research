import QiushiPlaneOrbit490Check0
import QiushiPlaneOrbit490Check1
import QiushiPlaneOrbit490Check2
import QiushiPlaneOrbit490Check3
import QiushiPlaneOrbit490Check4
import QiushiPlaneOrbit490Check5
import QiushiPlaneOrbit490Check6
import QiushiPlaneOrbit490Check7
import QiushiPlaneOrbit490Check8
import QiushiPlaneOrbit490Check9
import QiushiPlaneOrbit490Check10
import QiushiPlaneOrbit490Check11
import QiushiPlaneOrbit490Check12
import QiushiPlaneOrbit490Check13
import QiushiPlaneOrbit490Check14
import QiushiPlaneOrbit490Check15
import QiushiPlaneOrbit490Check16
import QiushiPlaneOrbit490Check17
import QiushiPlaneOrbit490Check18
import QiushiPlaneOrbit490Check19
import QiushiPlaneOrbit490Check20
import QiushiPlaneOrbit490Check21
import QiushiPlaneOrbit490Check22
import QiushiPlaneOrbit490Check23
import QiushiPlaneOrbit490Check24
import QiushiPlaneOrbit490Check25
import QiushiPlaneOrbit490Check26
import QiushiPlaneOrbit490Check27
import QiushiPlaneOrbit490Check28
import QiushiPlaneOrbit490Check29
import QiushiPlaneOrbit490Check30
import QiushiPlaneOrbit490Check31
import QiushiPlaneOrbit490Check32
import QiushiPlaneOrbit490Check33
import QiushiPlaneOrbit490Check34
import QiushiPlaneOrbit490Check35
import QiushiPlaneOrbit490Check36

namespace QiushiMatmul.PlaneOrbit.Orbit490

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

end QiushiMatmul.PlaneOrbit.Orbit490
