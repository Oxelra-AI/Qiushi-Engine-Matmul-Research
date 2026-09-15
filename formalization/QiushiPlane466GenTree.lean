import QiushiPlane466GenLeaf0000
import QiushiPlane466GenLeaf0001
import QiushiPlane466GenLeaf0002
import QiushiPlane466GenLeaf0003
import QiushiPlane466GenLeaf0004
import QiushiPlane466GenLeaf0005
import QiushiPlane466GenLeaf0006
import QiushiPlane466GenLeaf0007
import QiushiPlane466GenLeaf0008
import QiushiPlane466GenLeaf0009
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane466GenNoModel (x : Fin 50 → Int) (hroot : plane466GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 24 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 19 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 26 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 28 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 7 ≤ (0 : Int)
          ·
            exact plane466GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane466GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane466GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane466GenLeaf0003 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 30 ≤ (1 : Int)
      ·
        by_cases hbranch_LRL : x 12 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 21 ≤ (0 : Int)
          ·
            exact plane466GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane466GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane466GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane466GenLeaf0007 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 28 ≤ (0 : Int)
    ·
      exact plane466GenLeaf0008 x hroot (by omega) (by omega)
    ·
      exact plane466GenLeaf0009 x hroot (by omega) (by omega)

end QiushiMatmul
