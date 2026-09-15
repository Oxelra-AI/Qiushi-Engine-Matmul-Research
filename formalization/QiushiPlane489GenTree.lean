import QiushiPlane489GenLeaf0000
import QiushiPlane489GenLeaf0001
import QiushiPlane489GenLeaf0002
import QiushiPlane489GenLeaf0003
import QiushiPlane489GenLeaf0004
import QiushiPlane489GenLeaf0005
import QiushiPlane489GenLeaf0006
import QiushiPlane489GenLeaf0007
import QiushiPlane489GenLeaf0008
import QiushiPlane489GenLeaf0009
import QiushiPlane489GenLeaf0010
import QiushiPlane489GenLeaf0011
import QiushiPlane489GenLeaf0012
import QiushiPlane489GenLeaf0013
import QiushiPlane489GenLeaf0014
import QiushiPlane489GenLeaf0015
import QiushiPlane489GenLeaf0016
import QiushiPlane489GenLeaf0017
import QiushiPlane489GenLeaf0018
import QiushiPlane489GenLeaf0019
import QiushiPlane489GenLeaf0020
import QiushiPlane489GenLeaf0021
import QiushiPlane489GenLeaf0022
import QiushiPlane489GenLeaf0023
import QiushiPlane489GenLeaf0024
import QiushiPlane489GenLeaf0025
import QiushiPlane489GenLeaf0026
import QiushiPlane489GenLeaf0027
import QiushiPlane489GenLeaf0028
import QiushiPlane489GenLeaf0029
import QiushiPlane489GenLeaf0030
import QiushiPlane489GenLeaf0031
import QiushiPlane489GenLeaf0032
import QiushiPlane489GenLeaf0033
import QiushiPlane489GenLeaf0034
import QiushiPlane489GenLeaf0035
import QiushiPlane489GenLeaf0036
import QiushiPlane489GenLeaf0037
import QiushiPlane489GenLeaf0038
import QiushiPlane489GenLeaf0039
import QiushiPlane489GenLeaf0040
import QiushiPlane489GenLeaf0041
import QiushiPlane489GenLeaf0042
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane489GenNoModel (x : Fin 32 → Int) (hroot : plane489GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 14 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 9 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 31 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 25 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 10 ≤ (0 : Int)
          ·
            exact plane489GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLLR : x 18 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLRL : x 16 ≤ (0 : Int)
              ·
                exact plane489GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane489GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane489GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 23 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 12 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLLL : x 22 ≤ (0 : Int)
              ·
                exact plane489GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane489GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRLLR : x 18 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLLRL : x 10 ≤ (0 : Int)
                ·
                  exact plane489GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane489GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane489GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 7 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRRL : x 27 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRRR : x 24 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 12 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 17 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 22 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 28 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane489GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 15 ≤ (0 : Int)
        ·
          exact plane489GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRRR : x 5 ≤ (0 : Int)
          ·
            by_cases hbranch_LRRRL : x 26 ≤ (0 : Int)
            ·
              by_cases hbranch_LRRRLL : x 24 ≤ (0 : Int)
              ·
                exact plane489GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane489GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 26 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 7 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 30 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLLL : x 24 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLLR : x 16 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLRL : x 28 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 18 ≤ (0 : Int)
        ·
          by_cases hbranch_RLRL : x 31 ≤ (0 : Int)
          ·
            by_cases hbranch_RLRLL : x 22 ≤ (0 : Int)
            ·
              exact plane489GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLRLR : x 23 ≤ (0 : Int)
            ·
              by_cases hbranch_RLRLRL : x 9 ≤ (0 : Int)
              ·
                by_cases hbranch_RLRLRLL : x 12 ≤ (0 : Int)
                ·
                  exact plane489GenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane489GenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane489GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane489GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane489GenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 30 ≤ (0 : Int)
      ·
        by_cases hbranch_RRL : x 13 ≤ (0 : Int)
        ·
          exact plane489GenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RRLR : x 24 ≤ (0 : Int)
          ·
            exact plane489GenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RRR : x 22 ≤ (0 : Int)
        ·
          by_cases hbranch_RRRL : x 0 ≤ (1 : Int)
          ·
            exact plane489GenLeaf0040 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane489GenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane489GenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega)

end QiushiMatmul
