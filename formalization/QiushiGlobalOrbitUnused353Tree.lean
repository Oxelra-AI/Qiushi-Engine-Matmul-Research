import QiushiGlobalOrbitUnused353Leaf0000
import QiushiGlobalOrbitUnused353Leaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane353UnusedGenNoModel (x : Fin 20 → Int) (hroot : plane353UnusedGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 15 ≤ (0 : Int)
  ·
    exact plane353UnusedGenLeaf0000 x hroot (by omega)
  ·
    exact plane353UnusedGenLeaf0001 x hroot (by omega)

end QiushiMatmul
