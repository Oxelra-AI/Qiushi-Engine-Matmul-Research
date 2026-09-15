import QiushiPlane464GenLeaf0000
import QiushiPlane464GenLeaf0001
import QiushiPlane464GenLeaf0002
import QiushiPlane464GenLeaf0003
import QiushiPlane464GenLeaf0004
import QiushiPlane464GenLeaf0005
import QiushiPlane464GenLeaf0006
import QiushiPlane464GenLeaf0007
import QiushiPlane464GenLeaf0008
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane464GenNoModel (x : Fin 50 → Int) (hroot : plane464GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 1 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 15 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 5 ≤ (0 : Int)
      ·
        exact plane464GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 37 ≤ (0 : Int)
        ·
          exact plane464GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane464GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      exact plane464GenLeaf0003 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 49 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 40 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 19 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 18 ≤ (0 : Int)
          ·
            exact plane464GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane464GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane464GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane464GenLeaf0007 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane464GenLeaf0008 x hroot (by omega) (by omega)

end QiushiMatmul
