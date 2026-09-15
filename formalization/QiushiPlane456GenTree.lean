import QiushiPlane456GenLeaf0000
import QiushiPlane456GenLeaf0001
import QiushiPlane456GenLeaf0002
import QiushiPlane456GenLeaf0003
import QiushiPlane456GenLeaf0004
import QiushiPlane456GenLeaf0005
import QiushiPlane456GenLeaf0006
import QiushiPlane456GenLeaf0007
import QiushiPlane456GenLeaf0008
import QiushiPlane456GenLeaf0009
import QiushiPlane456GenLeaf0010
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane456GenNoModel (x : Fin 63 → Int) (hroot : plane456GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 24 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 31 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 57 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 54 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 9 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 10 ≤ (0 : Int)
            ·
              exact plane456GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane456GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLLR : x 4 ≤ (0 : Int)
            ·
              exact plane456GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane456GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane456GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 61 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 12 ≤ (0 : Int)
          ·
            exact plane456GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane456GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane456GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 6 ≤ (0 : Int)
      ·
        exact plane456GenLeaf0008 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane456GenLeaf0009 x hroot (by omega) (by omega) (by omega)
  ·
    exact plane456GenLeaf0010 x hroot (by omega)

end QiushiMatmul
