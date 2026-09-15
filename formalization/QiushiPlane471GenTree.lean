import QiushiPlane471GenLeaf0000
import QiushiPlane471GenLeaf0001
import QiushiPlane471GenLeaf0002
import QiushiPlane471GenLeaf0003
import QiushiPlane471GenLeaf0004
import QiushiPlane471GenLeaf0005
import QiushiPlane471GenLeaf0006
import QiushiPlane471GenLeaf0007
import QiushiPlane471GenLeaf0008
import QiushiPlane471GenLeaf0009
import QiushiPlane471GenLeaf0010
import QiushiPlane471GenLeaf0011
import QiushiPlane471GenLeaf0012
import QiushiPlane471GenLeaf0013
import QiushiPlane471GenLeaf0014
import QiushiPlane471GenLeaf0015
import QiushiPlane471GenLeaf0016
import QiushiPlane471GenLeaf0017
import QiushiPlane471GenLeaf0018
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane471GenNoModel (x : Fin 63 → Int) (hroot : plane471GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 48 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 14 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 38 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 12 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 20 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 43 ≤ (0 : Int)
            ·
              exact plane471GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane471GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane471GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane471GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane471GenLeaf0004 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 4 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 38 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 19 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 6 ≤ (0 : Int)
            ·
              exact plane471GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane471GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane471GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane471GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 8 ≤ (0 : Int)
        ·
          by_cases hbranch_LRRL : x 16 ≤ (0 : Int)
          ·
            by_cases hbranch_LRRLL : x 25 ≤ (0 : Int)
            ·
              by_cases hbranch_LRRLLL : x 22 ≤ (0 : Int)
              ·
                by_cases hbranch_LRRLLLL : x 38 ≤ (0 : Int)
                ·
                  by_cases hbranch_LRRLLLLL : x 40 ≤ (0 : Int)
                  ·
                    exact plane471GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane471GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane471GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane471GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane471GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRRLR : x 11 ≤ (0 : Int)
            ·
              by_cases hbranch_LRRLRL : x 33 ≤ (0 : Int)
              ·
                exact plane471GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane471GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane471GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane471GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega)
  ·
    exact plane471GenLeaf0018 x hroot (by omega)

end QiushiMatmul
