import QiushiPlane452GenLeaf0000
import QiushiPlane452GenLeaf0001
import QiushiPlane452GenLeaf0002
import QiushiPlane452GenLeaf0003
import QiushiPlane452GenLeaf0004
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane452GenNoModel (x : Fin 35 → Int) (hroot : plane452GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 8 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 10 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 7 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 0 ≤ (0 : Int)
        ·
          exact plane452GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane452GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane452GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane452GenLeaf0003 x hroot (by omega) (by omega)
  ·
    exact plane452GenLeaf0004 x hroot (by omega)

end QiushiMatmul
