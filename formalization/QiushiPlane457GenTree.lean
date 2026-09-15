import QiushiPlane457GenLeaf0000
import QiushiPlane457GenLeaf0001
import QiushiPlane457GenLeaf0002
import QiushiPlane457GenLeaf0003
import QiushiPlane457GenLeaf0004
import QiushiPlane457GenLeaf0005
import QiushiPlane457GenLeaf0006
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane457GenNoModel (x : Fin 49 → Int) (hroot : plane457GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 3 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 1 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 4 ≤ (0 : Int)
      ·
        exact plane457GenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane457GenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane457GenLeaf0002 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 23 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 26 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 35 ≤ (0 : Int)
        ·
          exact plane457GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane457GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane457GenLeaf0005 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane457GenLeaf0006 x hroot (by omega) (by omega)

end QiushiMatmul
