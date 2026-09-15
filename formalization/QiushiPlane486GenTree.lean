import QiushiPlane486GenLeaf0000
import QiushiPlane486GenLeaf0001
import QiushiPlane486GenLeaf0002
import QiushiPlane486GenLeaf0003
import QiushiPlane486GenLeaf0004
import QiushiPlane486GenLeaf0005
import QiushiPlane486GenLeaf0006
import QiushiPlane486GenLeaf0007
import QiushiPlane486GenLeaf0008
import QiushiPlane486GenLeaf0009
import QiushiPlane486GenLeaf0010
import QiushiPlane486GenLeaf0011
import QiushiPlane486GenLeaf0012
import QiushiPlane486GenLeaf0013
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane486GenNoModel (x : Fin 41 → Int) (hroot : plane486GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 22 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 21 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 18 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 31 ≤ (0 : Int)
        ·
          exact plane486GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane486GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane486GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 17 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 37 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 16 ≤ (0 : Int)
            ·
              exact plane486GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane486GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLLR : x 10 ≤ (0 : Int)
            ·
              exact plane486GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane486GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane486GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane486GenLeaf0008 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 16 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 3 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 10 ≤ (0 : Int)
        ·
          exact plane486GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane486GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 36 ≤ (0 : Int)
        ·
          exact plane486GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane486GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      exact plane486GenLeaf0013 x hroot (by omega) (by omega)

end QiushiMatmul
