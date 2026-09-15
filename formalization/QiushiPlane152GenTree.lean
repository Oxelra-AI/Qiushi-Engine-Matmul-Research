import QiushiPlane152GenLeaf0000
import QiushiPlane152GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane152GenNoModel (x : Fin 10 → Int) (hroot : plane152GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 0 ≤ (1 : Int)
  ·
    exact plane152GenLeaf0000 x hroot (by omega)
  ·
    exact plane152GenLeaf0001 x hroot (by omega)

end QiushiMatmul
