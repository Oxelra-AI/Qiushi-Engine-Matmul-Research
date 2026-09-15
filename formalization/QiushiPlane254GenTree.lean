import QiushiPlane254GenLeaf0000
import QiushiPlane254GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane254GenNoModel (x : Fin 18 → Int) (hroot : plane254GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 0 ≤ (1 : Int)
  ·
    exact plane254GenLeaf0000 x hroot (by omega)
  ·
    exact plane254GenLeaf0001 x hroot (by omega)

end QiushiMatmul
