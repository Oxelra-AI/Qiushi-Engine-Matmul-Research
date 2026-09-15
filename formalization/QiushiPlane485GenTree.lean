import QiushiPlane485GenLeaf0000
import QiushiPlane485GenLeaf0001
import QiushiPlane485GenLeaf0002
import QiushiPlane485GenLeaf0003
import QiushiPlane485GenLeaf0004
import QiushiPlane485GenLeaf0005
import QiushiPlane485GenLeaf0006
import QiushiPlane485GenLeaf0007
import QiushiPlane485GenLeaf0008
import QiushiPlane485GenLeaf0009
import QiushiPlane485GenLeaf0010
import QiushiPlane485GenLeaf0011
import QiushiPlane485GenLeaf0012
import QiushiPlane485GenLeaf0013
import QiushiPlane485GenLeaf0014
import QiushiPlane485GenLeaf0015
import QiushiPlane485GenLeaf0016
import QiushiPlane485GenLeaf0017
import QiushiPlane485GenLeaf0018
import QiushiPlane485GenLeaf0019
import QiushiPlane485GenLeaf0020
import QiushiPlane485GenLeaf0021
import QiushiPlane485GenLeaf0022
import QiushiPlane485GenLeaf0023
import QiushiPlane485GenLeaf0024
import QiushiPlane485GenLeaf0025
import QiushiPlane485GenLeaf0026
import QiushiPlane485GenLeaf0027
import QiushiPlane485GenLeaf0028
import QiushiPlane485GenLeaf0029
import QiushiPlane485GenLeaf0030
import QiushiPlane485GenLeaf0031
import QiushiPlane485GenLeaf0032
import QiushiPlane485GenLeaf0033
import QiushiPlane485GenLeaf0034
import QiushiPlane485GenLeaf0035
import QiushiPlane485GenLeaf0036
import QiushiPlane485GenLeaf0037
import QiushiPlane485GenLeaf0038
import QiushiPlane485GenLeaf0039
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane485GenNoModel (x : Fin 41 → Int) (hroot : plane485GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 28 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 21 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 14 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 11 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 39 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 17 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 10 ≤ (0 : Int)
              ·
                exact plane485GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLLLLR : x 24 ≤ (0 : Int)
                ·
                  exact plane485GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane485GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLLR : x 29 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLRL : x 18 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLRLL : x 26 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLRLLL : x 22 ≤ (0 : Int)
                  ·
                    exact plane485GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane485GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane485GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane485GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLRR : x 25 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLRRL : x 6 ≤ (0 : Int)
                ·
                  exact plane485GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane485GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane485GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 40 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 13 ≤ (0 : Int)
            ·
              exact plane485GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane485GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 29 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 13 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 15 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLLL : x 31 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLLLL : x 4 ≤ (0 : Int)
                ·
                  exact plane485GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane485GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane485GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRLR : x 1 ≤ (0 : Int)
            ·
              exact plane485GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane485GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 32 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 25 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 23 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 1 ≤ (0 : Int)
            ·
              exact plane485GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLLR : x 9 ≤ (0 : Int)
            ·
              exact plane485GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane485GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane485GenLeaf0026 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 19 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 22 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 0 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 35 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLLL : x 6 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLLL : x 32 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLLLL : x 29 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLLLLLLL : x 14 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLLLLLL : x 11 ≤ (0 : Int)
                    ·
                      exact plane485GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane485GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane485GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane485GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane485GenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLLLR : x 4 ≤ (0 : Int)
            ·
              exact plane485GenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane485GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane485GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 6 ≤ (0 : Int)
        ·
          exact plane485GenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane485GenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 18 ≤ (0 : Int)
      ·
        exact plane485GenLeaf0038 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane485GenLeaf0039 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
