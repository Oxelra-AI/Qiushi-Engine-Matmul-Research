import QiushiPlane480GenLeaf0000
import QiushiPlane480GenLeaf0001
import QiushiPlane480GenLeaf0002
import QiushiPlane480GenLeaf0003
import QiushiPlane480GenLeaf0004
import QiushiPlane480GenLeaf0005
import QiushiPlane480GenLeaf0006
import QiushiPlane480GenLeaf0007
import QiushiPlane480GenLeaf0008
import QiushiPlane480GenLeaf0009
import QiushiPlane480GenLeaf0010
import QiushiPlane480GenLeaf0011
import QiushiPlane480GenLeaf0012
import QiushiPlane480GenLeaf0013
import QiushiPlane480GenLeaf0014
import QiushiPlane480GenLeaf0015
import QiushiPlane480GenLeaf0016
import QiushiPlane480GenLeaf0017
import QiushiPlane480GenLeaf0018
import QiushiPlane480GenLeaf0019
import QiushiPlane480GenLeaf0020
import QiushiPlane480GenLeaf0021
import QiushiPlane480GenLeaf0022
import QiushiPlane480GenLeaf0023
import QiushiPlane480GenLeaf0024
import QiushiPlane480GenLeaf0025
import QiushiPlane480GenLeaf0026
import QiushiPlane480GenLeaf0027
import QiushiPlane480GenLeaf0028
import QiushiPlane480GenLeaf0029
import QiushiPlane480GenLeaf0030
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane480GenNoModel (x : Fin 26 → Int) (hroot : plane480GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 6 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 20 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 11 ≤ (0 : Int)
      ·
        exact plane480GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane480GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 13 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 11 ≤ (0 : Int)
        ·
          exact plane480GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane480GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane480GenLeaf0004 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 14 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 11 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 10 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 12 ≤ (0 : Int)
          ·
            exact plane480GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane480GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLLR : x 13 ≤ (0 : Int)
          ·
            exact plane480GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLLRR : x 12 ≤ (0 : Int)
            ·
              exact plane480GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane480GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 5 ≤ (0 : Int)
        ·
          by_cases hbranch_RLRL : x 12 ≤ (0 : Int)
          ·
            exact plane480GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLRLR : x 10 ≤ (0 : Int)
            ·
              exact plane480GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane480GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLRR : x 1 ≤ (0 : Int)
          ·
            by_cases hbranch_RLRRL : x 12 ≤ (0 : Int)
            ·
              exact plane480GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RLRRLR : x 10 ≤ (0 : Int)
              ·
                exact plane480GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane480GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLRRR : x 12 ≤ (0 : Int)
            ·
              by_cases hbranch_RLRRRL : x 17 ≤ (0 : Int)
              ·
                by_cases hbranch_RLRRRLL : x 10 ≤ (0 : Int)
                ·
                  exact plane480GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane480GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_RLRRRLR : x 10 ≤ (0 : Int)
                ·
                  exact plane480GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane480GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RLRRRR : x 10 ≤ (0 : Int)
              ·
                by_cases hbranch_RLRRRRL : x 13 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLRRRRLL : x 15 ≤ (0 : Int)
                  ·
                    exact plane480GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane480GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane480GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane480GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 12 ≤ (0 : Int)
      ·
        by_cases hbranch_RRL : x 10 ≤ (0 : Int)
        ·
          by_cases hbranch_RRLL : x 25 ≤ (0 : Int)
          ·
            by_cases hbranch_RRLLL : x 13 ≤ (0 : Int)
            ·
              exact plane480GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane480GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane480GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RRLR : x 13 ≤ (0 : Int)
          ·
            exact plane480GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane480GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RRR : x 13 ≤ (0 : Int)
        ·
          exact plane480GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane480GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega)

end QiushiMatmul
