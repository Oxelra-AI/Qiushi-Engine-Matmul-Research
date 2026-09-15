import QiushiGlobalOrbitUnused372Leaf0000
import QiushiGlobalOrbitUnused372Leaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane372UnusedGenNoModel (x : Fin 26 → Int) (hroot : plane372UnusedGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 25 ≤ (0 : Int)
  ·
    exact plane372UnusedGenLeaf0000 x hroot (by omega)
  ·
    exact plane372UnusedGenLeaf0001 x hroot (by omega)

end QiushiMatmul
