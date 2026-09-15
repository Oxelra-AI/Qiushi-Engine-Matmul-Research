import QiushiPlane465GenLeaf0000
import QiushiPlane465GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane465GenNoModel (x : Fin 57 → Int) (hroot : plane465GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 44 ≤ (0 : Int)
  ·
    exact plane465GenLeaf0000 x hroot (by omega)
  ·
    exact plane465GenLeaf0001 x hroot (by omega)

end QiushiMatmul
