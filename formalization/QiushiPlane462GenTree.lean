import QiushiPlane462GenLeaf0000
import QiushiPlane462GenLeaf0001
import QiushiPlane462GenLeaf0002
import QiushiPlane462GenLeaf0003
import QiushiPlane462GenLeaf0004
import QiushiPlane462GenLeaf0005
import QiushiPlane462GenLeaf0006
import QiushiPlane462GenLeaf0007
import QiushiPlane462GenLeaf0008
import QiushiPlane462GenLeaf0009
import QiushiPlane462GenLeaf0010
import QiushiPlane462GenLeaf0011
import QiushiPlane462GenLeaf0012
import QiushiPlane462GenLeaf0013
import QiushiPlane462GenLeaf0014
import QiushiPlane462GenLeaf0015
import QiushiPlane462GenLeaf0016
import QiushiPlane462GenLeaf0017
import QiushiPlane462GenLeaf0018
import QiushiPlane462GenLeaf0019
import QiushiPlane462GenLeaf0020
import QiushiPlane462GenLeaf0021
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane462GenNoModel (x : Fin 62 → Int) (hroot : plane462GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 3 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 34 ≤ (1 : Int)
    ·
      by_cases hbranch_LL : x 28 ≤ (0 : Int)
      ·
        exact plane462GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 43 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 2 ≤ (0 : Int)
          ·
            exact plane462GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane462GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane462GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      exact plane462GenLeaf0004 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 5 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 2 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 43 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLLL : x 9 ≤ (0 : Int)
            ·
              exact plane462GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane462GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane462GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane462GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 45 ≤ (0 : Int)
        ·
          exact plane462GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane462GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 24 ≤ (0 : Int)
      ·
        by_cases hbranch_RRL : x 45 ≤ (0 : Int)
        ·
          exact plane462GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane462GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RRR : x 27 ≤ (0 : Int)
        ·
          by_cases hbranch_RRRL : x 34 ≤ (1 : Int)
          ·
            exact plane462GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane462GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RRRR : x 9 ≤ (0 : Int)
          ·
            by_cases hbranch_RRRRL : x 16 ≤ (0 : Int)
            ·
              exact plane462GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RRRRLR : x 1 ≤ (0 : Int)
              ·
                by_cases hbranch_RRRRLRL : x 34 ≤ (1 : Int)
                ·
                  exact plane462GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane462GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane462GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RRRRR : x 6 ≤ (0 : Int)
            ·
              by_cases hbranch_RRRRRL : x 34 ≤ (1 : Int)
              ·
                exact plane462GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane462GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane462GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end QiushiMatmul
