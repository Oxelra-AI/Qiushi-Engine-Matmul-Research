import QiushiGlobalOrbitUnused305Leaf0000
import QiushiGlobalOrbitUnused305Leaf0001
import QiushiGlobalOrbitUnused305Leaf0002
import QiushiGlobalOrbitUnused305Leaf0003
import QiushiGlobalOrbitUnused305Leaf0004
import QiushiGlobalOrbitUnused305Leaf0005
import QiushiGlobalOrbitUnused305Leaf0006
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane305UnusedGenNoModel (x : Fin 30 → Int) (hroot : plane305UnusedGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 2 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 7 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 15 ≤ (0 : Int)
      ·
        exact plane305UnusedGenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane305UnusedGenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 14 ≤ (0 : Int)
      ·
        exact plane305UnusedGenLeaf0002 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane305UnusedGenLeaf0003 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 9 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 13 ≤ (0 : Int)
      ·
        exact plane305UnusedGenLeaf0004 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane305UnusedGenLeaf0005 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane305UnusedGenLeaf0006 x hroot (by omega) (by omega)

end QiushiMatmul
