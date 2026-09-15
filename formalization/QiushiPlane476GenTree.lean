import QiushiPlane476GenLeaf0000
import QiushiPlane476GenLeaf0001
import QiushiPlane476GenLeaf0002
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane476GenNoModel (x : Fin 50 → Int) (hroot : plane476GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 35 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 11 ≤ (0 : Int)
    ·
      exact plane476GenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane476GenLeaf0001 x hroot (by omega) (by omega)
  ·
    exact plane476GenLeaf0002 x hroot (by omega)

end QiushiMatmul
