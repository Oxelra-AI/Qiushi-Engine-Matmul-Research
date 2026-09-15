import QiushiPlane467GenLeaf0000
import QiushiPlane467GenLeaf0001
import QiushiPlane467GenLeaf0002
import QiushiPlane467GenLeaf0003
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane467GenNoModel (x : Fin 59 → Int) (hroot : plane467GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 57 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 7 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 24 ≤ (0 : Int)
      ·
        exact plane467GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane467GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane467GenLeaf0002 x hroot (by omega) (by omega)
  ·
    exact plane467GenLeaf0003 x hroot (by omega)

end QiushiMatmul
