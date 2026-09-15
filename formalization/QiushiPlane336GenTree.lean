import QiushiPlane336GenLeaf0000
import QiushiPlane336GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane336GenNoModel (x : Fin 18 → Int) (hroot : plane336GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 1 ≤ (1 : Int)
  ·
    exact plane336GenLeaf0000 x hroot (by omega)
  ·
    exact plane336GenLeaf0001 x hroot (by omega)

end QiushiMatmul
