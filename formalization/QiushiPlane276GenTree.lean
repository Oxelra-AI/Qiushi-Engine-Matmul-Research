import QiushiPlane276GenLeaf0000
import QiushiPlane276GenLeaf0001
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane276GenNoModel (x : Fin 17 → Int) (hroot : plane276GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 2 ≤ (1 : Int)
  ·
    exact plane276GenLeaf0000 x hroot (by omega)
  ·
    exact plane276GenLeaf0001 x hroot (by omega)

end QiushiMatmul
