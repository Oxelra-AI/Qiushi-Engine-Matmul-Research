import QiushiPlane454GenLeaf0000
import QiushiPlane454GenLeaf0001
import QiushiPlane454GenLeaf0002
import QiushiPlane454GenLeaf0003
import QiushiPlane454GenLeaf0004
import QiushiPlane454GenLeaf0005
import QiushiPlane454GenLeaf0006
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane454GenNoModel (x : Fin 55 → Int) (hroot : plane454GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 2 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 4 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 12 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 26 ≤ (0 : Int)
        ·
          exact plane454GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane454GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane454GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 5 ≤ (0 : Int)
      ·
        exact plane454GenLeaf0003 x hroot (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 16 ≤ (0 : Int)
        ·
          exact plane454GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane454GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega)
  ·
    exact plane454GenLeaf0006 x hroot (by omega)

end QiushiMatmul
