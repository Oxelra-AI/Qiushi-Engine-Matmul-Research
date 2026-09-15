import QiushiPlane267GenLeaf0000
import QiushiPlane267GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane267GenNoModel (x : Fin 20 → Int) (hroot : plane267GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 10 ≤ (0 : Int)
  ·
    exact plane267GenLeaf0000 x hroot (by omega)
  ·
    exact plane267GenLeaf0001 x hroot (by omega)

end QiushiMatmul
