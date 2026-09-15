import QiushiPlane315GenLeaf0000
import QiushiPlane315GenLeaf0001
import QiushiPlane315GenLeaf0002
import QiushiPlane315GenLeaf0003
import QiushiPlane315GenLeaf0004
import QiushiPlane315GenLeaf0005
import QiushiPlane315GenLeaf0006
import QiushiPlane315GenLeaf0007
import QiushiPlane315GenLeaf0008
import QiushiPlane315GenLeaf0009
import QiushiPlane315GenLeaf0010
import QiushiPlane315GenLeaf0011
import QiushiPlane315GenLeaf0012
import QiushiPlane315GenLeaf0013
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane315GenNoModel (x : Fin 28 → Int) (hroot : plane315GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 5 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 2 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 12 ≤ (0 : Int)
      ·
        exact plane315GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 4 ≤ (1 : Int)
        ·
          by_cases hbranch_LLRL : x 0 ≤ (1 : Int)
          ·
            exact plane315GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane315GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 21 ≤ (0 : Int)
          ·
            exact plane315GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane315GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 10 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 7 ≤ (1 : Int)
        ·
          by_cases hbranch_LRLL : x 6 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 3 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLLLL : x 8 ≤ (1 : Int)
              ·
                exact plane315GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane315GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane315GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane315GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane315GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 8 ≤ (1 : Int)
        ·
          exact plane315GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane315GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 1 ≤ (0 : Int)
    ·
      exact plane315GenLeaf0012 x hroot (by omega) (by omega)
    ·
      exact plane315GenLeaf0013 x hroot (by omega) (by omega)

end QiushiMatmul
