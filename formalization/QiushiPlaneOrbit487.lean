import QiushiPlaneOrbit487Check0
import QiushiPlaneOrbit487Check1
import QiushiPlaneOrbit487Check2
import QiushiPlaneOrbit487Check3
import QiushiPlaneOrbit487Check4
import QiushiPlaneOrbit487Check5
import QiushiPlaneOrbit487Check6
import QiushiPlaneOrbit487Check7
import QiushiPlaneOrbit487Check8
import QiushiPlaneOrbit487Check9
import QiushiPlaneOrbit487Check10
import QiushiPlaneOrbit487Check11
import QiushiPlaneOrbit487Check12
import QiushiPlaneOrbit487Check13
import QiushiPlaneOrbit487Check14
import QiushiPlaneOrbit487Check15
import QiushiPlaneOrbit487Check16
import QiushiPlaneOrbit487Check17
import QiushiPlaneOrbit487Check18
import QiushiPlaneOrbit487Check19
import QiushiPlaneOrbit487Check20
import QiushiPlaneOrbit487Check21
import QiushiPlaneOrbit487Check22
import QiushiPlaneOrbit487Check23
import QiushiPlaneOrbit487Check24
import QiushiPlaneOrbit487Check25
import QiushiPlaneOrbit487Check26
import QiushiPlaneOrbit487Check27

namespace QiushiMatmul.PlaneOrbit.Orbit487

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

end QiushiMatmul.PlaneOrbit.Orbit487
