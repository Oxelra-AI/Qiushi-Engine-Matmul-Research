import QiushiPlane426GenLeaf0000
import QiushiPlane426GenLeaf0001
import QiushiPlane426GenLeaf0002
import QiushiPlane426GenLeaf0003
import QiushiPlane426GenLeaf0004
import QiushiPlane426GenLeaf0005
import QiushiPlane426GenLeaf0006
import QiushiPlane426GenLeaf0007
import QiushiPlane426GenLeaf0008
import QiushiPlane426GenLeaf0009
import QiushiPlane426GenLeaf0010
import QiushiPlane426GenLeaf0011
import QiushiPlane426GenLeaf0012
import QiushiPlane426GenLeaf0013
import QiushiPlane426GenLeaf0014
import QiushiPlane426GenLeaf0015
import QiushiPlane426GenLeaf0016
import QiushiPlane426GenLeaf0017
import QiushiPlane426GenLeaf0018
import QiushiPlane426GenLeaf0019
import QiushiPlane426GenLeaf0020
import QiushiPlane426GenLeaf0021
import QiushiPlane426GenLeaf0022
import QiushiPlane426GenLeaf0023
import QiushiPlane426GenLeaf0024
import QiushiPlane426GenLeaf0025
import QiushiPlane426GenLeaf0026
import QiushiPlane426GenLeaf0027
import QiushiPlane426GenLeaf0028
import QiushiPlane426GenLeaf0029
import QiushiPlane426GenLeaf0030
import QiushiPlane426GenLeaf0031
import QiushiPlane426GenLeaf0032
import QiushiPlane426GenLeaf0033
import QiushiPlane426GenLeaf0034
import QiushiPlane426GenLeaf0035
import QiushiPlane426GenLeaf0036
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane426GenNoModel (x : Fin 58 → Int) (hroot : plane426GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 43 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 14 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 1 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 13 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 37 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 21 ≤ (0 : Int)
            ·
              exact plane426GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLLR : x 35 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane426GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 21 ≤ (0 : Int)
          ·
            exact plane426GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane426GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 35 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 10 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLLL : x 34 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRLLR : x 20 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLRLLRR : x 57 ≤ (0 : Int)
                ·
                  exact plane426GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane426GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRLR : x 29 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLRL : x 20 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLRLRLR : x 11 ≤ (0 : Int)
                ·
                  exact plane426GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane426GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane426GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 13 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRRL : x 20 ≤ (0 : Int)
            ·
              exact plane426GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane426GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane426GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 42 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 18 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 56 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 11 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLLLL : x 6 ≤ (0 : Int)
              ·
                by_cases hbranch_LRLLLLL : x 51 ≤ (0 : Int)
                ·
                  by_cases hbranch_LRLLLLLL : x 49 ≤ (0 : Int)
                  ·
                    exact plane426GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane426GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane426GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LRLLLR : x 49 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane426GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRLR : x 49 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLRL : x 27 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLRLL : x 35 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LRLRLR : x 37 ≤ (0 : Int)
              ·
                exact plane426GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane426GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLRR : x 0 ≤ (1 : Int)
            ·
              exact plane426GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane426GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane426GenLeaf0031 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 34 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 37 ≤ (0 : Int)
      ·
        exact plane426GenLeaf0032 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane426GenLeaf0033 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 49 ≤ (0 : Int)
      ·
        by_cases hbranch_RRL : x 11 ≤ (0 : Int)
        ·
          exact plane426GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane426GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane426GenLeaf0036 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
