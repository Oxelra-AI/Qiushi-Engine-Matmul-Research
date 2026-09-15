import QiushiPlane488GenLeaf0000
import QiushiPlane488GenLeaf0001
import QiushiPlane488GenLeaf0002
import QiushiPlane488GenLeaf0003
import QiushiPlane488GenLeaf0004
import QiushiPlane488GenLeaf0005
import QiushiPlane488GenLeaf0006
import QiushiPlane488GenLeaf0007
import QiushiPlane488GenLeaf0008
import QiushiPlane488GenLeaf0009
import QiushiPlane488GenLeaf0010
import QiushiPlane488GenLeaf0011
import QiushiPlane488GenLeaf0012
import QiushiPlane488GenLeaf0013
import QiushiPlane488GenLeaf0014
import QiushiPlane488GenLeaf0015
import QiushiPlane488GenLeaf0016
import QiushiPlane488GenLeaf0017
import QiushiPlane488GenLeaf0018
import QiushiPlane488GenLeaf0019
import QiushiPlane488GenLeaf0020
import QiushiPlane488GenLeaf0021
import QiushiPlane488GenLeaf0022
import QiushiPlane488GenLeaf0023
import QiushiPlane488GenLeaf0024
import QiushiPlane488GenLeaf0025
import QiushiPlane488GenLeaf0026
import QiushiPlane488GenLeaf0027
import QiushiPlane488GenLeaf0028
import QiushiPlane488GenLeaf0029
import QiushiPlane488GenLeaf0030
import QiushiPlane488GenLeaf0031
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane488GenNoModel (x : Fin 41 → Int) (hroot : plane488GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 27 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 15 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 20 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 25 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 13 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 24 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 16 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 4 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 37 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLLLLLLL : x 5 ≤ (0 : Int)
                    ·
                      exact plane488GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane488GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane488GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane488GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLLR : x 23 ≤ (0 : Int)
              ·
                exact plane488GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane488GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 1 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 6 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRLL : x 3 ≤ (0 : Int)
              ·
                exact plane488GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane488GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLRR : x 6 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRRL : x 16 ≤ (0 : Int)
              ·
                exact plane488GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLRRR : x 21 ≤ (0 : Int)
              ·
                exact plane488GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 39 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 31 ≤ (0 : Int)
          ·
            exact plane488GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane488GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane488GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 14 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 24 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 25 ≤ (0 : Int)
          ·
            exact plane488GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane488GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane488GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 28 ≤ (0 : Int)
        ·
          exact plane488GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane488GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 19 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 16 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 22 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 40 ≤ (0 : Int)
          ·
            exact plane488GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLLLR : x 35 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLRL : x 6 ≤ (0 : Int)
              ·
                exact plane488GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane488GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane488GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane488GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 39 ≤ (0 : Int)
        ·
          exact plane488GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane488GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 38 ≤ (0 : Int)
      ·
        exact plane488GenLeaf0030 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane488GenLeaf0031 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
