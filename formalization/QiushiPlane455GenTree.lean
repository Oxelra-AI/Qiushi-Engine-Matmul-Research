import QiushiPlane455GenLeaf0000
import QiushiPlane455GenLeaf0001
import QiushiPlane455GenLeaf0002
import QiushiPlane455GenLeaf0003
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane455GenNoModel (x : Fin 48 → Int) (hroot : plane455GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 14 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 42 ≤ (0 : Int)
    ·
      exact plane455GenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane455GenLeaf0001 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 8 ≤ (0 : Int)
    ·
      exact plane455GenLeaf0002 x hroot (by omega) (by omega)
    ·
      exact plane455GenLeaf0003 x hroot (by omega) (by omega)

end QiushiMatmul
