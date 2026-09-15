import QiushiPlane470GenLeaf0000
import QiushiPlane470GenLeaf0001
import QiushiPlane470GenLeaf0002
import QiushiPlane470GenLeaf0003
import QiushiPlane470GenLeaf0004
import QiushiPlane470GenLeaf0005
import QiushiPlane470GenLeaf0006
import QiushiPlane470GenLeaf0007
import QiushiPlane470GenLeaf0008
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane470GenNoModel (x : Fin 63 → Int) (hroot : plane470GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 12 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 60 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 25 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 15 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 9 ≤ (0 : Int)
            ·
              exact plane470GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLLR : x 23 ≤ (0 : Int)
              ·
                exact plane470GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane470GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane470GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane470GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane470GenLeaf0005 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane470GenLeaf0006 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 18 ≤ (0 : Int)
    ·
      exact plane470GenLeaf0007 x hroot (by omega) (by omega)
    ·
      exact plane470GenLeaf0008 x hroot (by omega) (by omega)

end QiushiMatmul
