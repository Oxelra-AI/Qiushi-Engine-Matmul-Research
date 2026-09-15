import QiushiPlane295GenLeaf0000
import QiushiPlane295GenLeaf0001
import QiushiPlane295GenLeaf0002
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane295GenNoModel (x : Fin 24 → Int) (hroot : plane295GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 2 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 4 ≤ (0 : Int)
    ·
      exact plane295GenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane295GenLeaf0001 x hroot (by omega) (by omega)
  ·
    exact plane295GenLeaf0002 x hroot (by omega)

end QiushiMatmul
