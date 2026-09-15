import QiushiPlane473GenLeaf0000
import QiushiPlane473GenLeaf0001
import QiushiPlane473GenLeaf0002
import QiushiPlane473GenLeaf0003
import QiushiPlane473GenLeaf0004
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane473GenNoModel (x : Fin 59 → Int) (hroot : plane473GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 40 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 14 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 44 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 20 ≤ (0 : Int)
        ·
          exact plane473GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane473GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane473GenLeaf0002 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane473GenLeaf0003 x hroot (by omega) (by omega)
  ·
    exact plane473GenLeaf0004 x hroot (by omega)

end QiushiMatmul
