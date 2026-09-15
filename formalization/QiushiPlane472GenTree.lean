import QiushiPlane472GenLeaf0000
import QiushiPlane472GenLeaf0001
import QiushiPlane472GenLeaf0002
import QiushiPlane472GenLeaf0003
import QiushiPlane472GenLeaf0004
import QiushiPlane472GenLeaf0005
import QiushiPlane472GenLeaf0006
import QiushiPlane472GenLeaf0007
import QiushiPlane472GenLeaf0008
import QiushiPlane472GenLeaf0009
import QiushiPlane472GenLeaf0010
import QiushiPlane472GenLeaf0011
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane472GenNoModel (x : Fin 62 → Int) (hroot : plane472GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 60 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 4 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 33 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 11 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 21 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 51 ≤ (0 : Int)
            ·
              exact plane472GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane472GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane472GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 28 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 17 ≤ (0 : Int)
            ·
              exact plane472GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLRLR : x 26 ≤ (0 : Int)
              ·
                exact plane472GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane472GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane472GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane472GenLeaf0007 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane472GenLeaf0008 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 6 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 5 ≤ (0 : Int)
      ·
        exact plane472GenLeaf0009 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane472GenLeaf0010 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane472GenLeaf0011 x hroot (by omega) (by omega)

end QiushiMatmul
