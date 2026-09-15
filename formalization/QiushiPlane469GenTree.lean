import QiushiPlane469GenLeaf0000
import QiushiPlane469GenLeaf0001
import QiushiPlane469GenLeaf0002
import QiushiPlane469GenLeaf0003
import QiushiPlane469GenLeaf0004
import QiushiPlane469GenLeaf0005
import QiushiPlane469GenLeaf0006
import QiushiPlane469GenLeaf0007
import QiushiPlane469GenLeaf0008
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane469GenNoModel (x : Fin 60 → Int) (hroot : plane469GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 34 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 13 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 8 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 54 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 40 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 45 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 5 ≤ (0 : Int)
              ·
                exact plane469GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLLLLR : x 31 ≤ (0 : Int)
                ·
                  exact plane469GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane469GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane469GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane469GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane469GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane469GenLeaf0006 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane469GenLeaf0007 x hroot (by omega) (by omega)
  ·
    exact plane469GenLeaf0008 x hroot (by omega)

end QiushiMatmul
