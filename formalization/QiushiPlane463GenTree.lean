import QiushiPlane463GenLeaf0000
import QiushiPlane463GenLeaf0001
import QiushiPlane463GenLeaf0002
import QiushiPlane463GenLeaf0003
import QiushiPlane463GenLeaf0004
import QiushiPlane463GenLeaf0005
import QiushiPlane463GenLeaf0006
import QiushiPlane463GenLeaf0007
import QiushiPlane463GenLeaf0008
import QiushiPlane463GenLeaf0009
import QiushiPlane463GenLeaf0010
import QiushiPlane463GenLeaf0011
import QiushiPlane463GenLeaf0012
import QiushiPlane463GenLeaf0013
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane463GenNoModel (x : Fin 63 → Int) (hroot : plane463GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 15 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 24 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 60 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 21 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 19 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 47 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 22 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 20 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 2 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLLLLLLL : x 29 ≤ (0 : Int)
                    ·
                      exact plane463GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane463GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane463GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane463GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane463GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane463GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane463GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 35 ≤ (0 : Int)
          ·
            exact plane463GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane463GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane463GenLeaf0009 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane463GenLeaf0010 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 23 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 33 ≤ (0 : Int)
      ·
        exact plane463GenLeaf0011 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane463GenLeaf0012 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane463GenLeaf0013 x hroot (by omega) (by omega)

end QiushiMatmul
