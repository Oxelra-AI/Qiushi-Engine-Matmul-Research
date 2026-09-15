import QiushiPlane468GenLeaf0000
import QiushiPlane468GenLeaf0001
import QiushiPlane468GenLeaf0002
import QiushiPlane468GenLeaf0003
import QiushiPlane468GenLeaf0004
import QiushiPlane468GenLeaf0005
import QiushiPlane468GenLeaf0006
import QiushiPlane468GenLeaf0007
import QiushiPlane468GenLeaf0008
import QiushiPlane468GenLeaf0009
import QiushiPlane468GenLeaf0010
import QiushiPlane468GenLeaf0011
import QiushiPlane468GenLeaf0012
import QiushiPlane468GenLeaf0013
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane468GenNoModel (x : Fin 62 → Int) (hroot : plane468GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 28 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 51 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 47 ≤ (0 : Int)
      ·
        exact plane468GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane468GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 15 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 2 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 33 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 4 ≤ (0 : Int)
            ·
              exact plane468GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane468GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane468GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRLR : x 1 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLRL : x 49 ≤ (0 : Int)
            ·
              exact plane468GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane468GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLRR : x 11 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLRRL : x 40 ≤ (0 : Int)
              ·
                exact plane468GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane468GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane468GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane468GenLeaf0010 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 36 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 55 ≤ (0 : Int)
      ·
        exact plane468GenLeaf0011 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane468GenLeaf0012 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane468GenLeaf0013 x hroot (by omega) (by omega)

end QiushiMatmul
