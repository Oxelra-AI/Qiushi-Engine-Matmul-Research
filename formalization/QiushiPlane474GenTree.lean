import QiushiPlane474GenLeaf0000
import QiushiPlane474GenLeaf0001
import QiushiPlane474GenLeaf0002
import QiushiPlane474GenLeaf0003
import QiushiPlane474GenLeaf0004
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane474GenNoModel (x : Fin 60 → Int) (hroot : plane474GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 44 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 43 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 22 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 37 ≤ (0 : Int)
        ·
          exact plane474GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane474GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane474GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane474GenLeaf0003 x hroot (by omega) (by omega)
  ·
    exact plane474GenLeaf0004 x hroot (by omega)

end QiushiMatmul
