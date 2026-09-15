import QiushiGlobalOrbitUnused371Leaf0000
import QiushiGlobalOrbitUnused371Leaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane371UnusedGenNoModel (x : Fin 18 → Int) (hroot : plane371UnusedGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 0 ≤ (1 : Int)
  ·
    exact plane371UnusedGenLeaf0000 x hroot (by omega)
  ·
    exact plane371UnusedGenLeaf0001 x hroot (by omega)

end QiushiMatmul
