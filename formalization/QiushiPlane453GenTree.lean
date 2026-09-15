import QiushiPlane453GenLeaf0000
import QiushiPlane453GenLeaf0001
import QiushiPlane453GenLeaf0002
import QiushiPlane453GenLeaf0003
import QiushiPlane453GenLeaf0004
import QiushiPlane453GenLeaf0005
import QiushiPlane453GenLeaf0006
import QiushiPlane453GenLeaf0007
import QiushiPlane453GenLeaf0008
import QiushiPlane453GenLeaf0009
import QiushiPlane453GenLeaf0010
import QiushiPlane453GenLeaf0011
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane453GenNoModel (x : Fin 50 → Int) (hroot : plane453GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 35 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 5 ≤ (1 : Int)
    ·
      by_cases hbranch_LL : x 15 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 9 ≤ (0 : Int)
        ·
          exact plane453GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane453GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 1 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 17 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 11 ≤ (0 : Int)
            ·
              exact plane453GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane453GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane453GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane453GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 41 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 1 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 27 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLLL : x 49 ≤ (0 : Int)
            ·
              exact plane453GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane453GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane453GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane453GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane453GenLeaf0010 x hroot (by omega) (by omega) (by omega)
  ·
    exact plane453GenLeaf0011 x hroot (by omega)

end QiushiMatmul
