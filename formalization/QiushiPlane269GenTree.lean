import QiushiPlane269GenLeaf0000
import QiushiPlane269GenLeaf0001
import QiushiPlane269GenLeaf0002
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane269GenNoModel (x : Fin 21 → Int) (hroot : plane269GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 1 ≤ (1 : Int)
  ·
    by_cases hbranch_L : x 0 ≤ (2 : Int)
    ·
      exact plane269GenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane269GenLeaf0001 x hroot (by omega) (by omega)
  ·
    exact plane269GenLeaf0002 x hroot (by omega)

end QiushiMatmul
