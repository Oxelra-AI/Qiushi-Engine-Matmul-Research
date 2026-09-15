import QiushiPlane475GenLeaf0000
import QiushiPlane475GenLeaf0001
import QiushiPlane475GenLeaf0002
import QiushiPlane475GenLeaf0003
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane475GenNoModel (x : Fin 56 → Int) (hroot : plane475GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 34 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 2 ≤ (0 : Int)
    ·
      exact plane475GenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane475GenLeaf0001 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 27 ≤ (0 : Int)
    ·
      exact plane475GenLeaf0002 x hroot (by omega) (by omega)
    ·
      exact plane475GenLeaf0003 x hroot (by omega) (by omega)

end QiushiMatmul
