import QiushiPlane425GenLeaf0000
import QiushiPlane425GenLeaf0001
import QiushiPlane425GenLeaf0002
import QiushiPlane425GenLeaf0003
import QiushiPlane425GenLeaf0004
import QiushiPlane425GenLeaf0005
import QiushiPlane425GenLeaf0006
import QiushiPlane425GenLeaf0007
import QiushiPlane425GenLeaf0008
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane425GenNoModel (x : Fin 58 → Int) (hroot : plane425GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 17 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 8 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 47 ≤ (0 : Int)
      ·
        exact plane425GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane425GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane425GenLeaf0002 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 9 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 43 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 20 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 6 ≤ (0 : Int)
          ·
            exact plane425GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane425GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane425GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 12 ≤ (0 : Int)
        ·
          exact plane425GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane425GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      exact plane425GenLeaf0008 x hroot (by omega) (by omega)

end QiushiMatmul
