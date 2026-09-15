import QiushiPlane458GenLeaf0000
import QiushiPlane458GenLeaf0001
import QiushiPlane458GenLeaf0002
import QiushiPlane458GenLeaf0003
import QiushiPlane458GenLeaf0004
import QiushiPlane458GenLeaf0005
import QiushiPlane458GenLeaf0006
import QiushiPlane458GenLeaf0007
import QiushiPlane458GenLeaf0008
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane458GenNoModel (x : Fin 56 → Int) (hroot : plane458GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 46 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 30 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 31 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 9 ≤ (0 : Int)
        ·
          exact plane458GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane458GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane458GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 10 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 3 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 40 ≤ (0 : Int)
          ·
            exact plane458GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane458GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane458GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane458GenLeaf0006 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 10 ≤ (0 : Int)
    ·
      exact plane458GenLeaf0007 x hroot (by omega) (by omega)
    ·
      exact plane458GenLeaf0008 x hroot (by omega) (by omega)

end QiushiMatmul
