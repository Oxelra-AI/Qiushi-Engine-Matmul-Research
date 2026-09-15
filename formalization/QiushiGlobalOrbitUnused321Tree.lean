import QiushiGlobalOrbitUnused321Leaf0000
import QiushiGlobalOrbitUnused321Leaf0001
import QiushiGlobalOrbitUnused321Leaf0002
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane321UnusedGenNoModel (x : Fin 26 → Int) (hroot : plane321UnusedGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 21 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 9 ≤ (0 : Int)
    ·
      exact plane321UnusedGenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane321UnusedGenLeaf0001 x hroot (by omega) (by omega)
  ·
    exact plane321UnusedGenLeaf0002 x hroot (by omega)

end QiushiMatmul
