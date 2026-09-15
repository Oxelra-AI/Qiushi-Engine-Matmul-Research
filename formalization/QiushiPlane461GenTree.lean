import QiushiPlane461GenLeaf0000
import QiushiPlane461GenLeaf0001
import QiushiPlane461GenLeaf0002
import QiushiPlane461GenLeaf0003
import QiushiPlane461GenLeaf0004
import QiushiPlane461GenLeaf0005
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane461GenNoModel (x : Fin 62 → Int) (hroot : plane461GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 16 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 7 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 22 ≤ (0 : Int)
      ·
        exact plane461GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane461GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane461GenLeaf0002 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 48 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 21 ≤ (0 : Int)
      ·
        exact plane461GenLeaf0003 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane461GenLeaf0004 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane461GenLeaf0005 x hroot (by omega) (by omega)

end QiushiMatmul
