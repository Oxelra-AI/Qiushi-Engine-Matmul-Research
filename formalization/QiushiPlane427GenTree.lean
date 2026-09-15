import QiushiPlane427GenLeaf0000
import QiushiPlane427GenLeaf0001
import QiushiPlane427GenLeaf0002
import QiushiPlane427GenLeaf0003
import QiushiPlane427GenLeaf0004
import QiushiPlane427GenLeaf0005
import QiushiPlane427GenLeaf0006
import QiushiPlane427GenLeaf0007
import QiushiPlane427GenLeaf0008
import QiushiPlane427GenLeaf0009
import QiushiPlane427GenLeaf0010
import QiushiPlane427GenLeaf0011
import QiushiPlane427GenLeaf0012
import QiushiPlane427GenLeaf0013
import QiushiPlane427GenLeaf0014
import QiushiPlane427GenLeaf0015
import QiushiPlane427GenLeaf0016
import QiushiPlane427GenLeaf0017
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane427GenNoModel (x : Fin 50 → Int) (hroot : plane427GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 26 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 15 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 35 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 45 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 18 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 28 ≤ (0 : Int)
            ·
              exact plane427GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane427GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane427GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 14 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 37 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRLL : x 32 ≤ (0 : Int)
              ·
                exact plane427GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane427GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane427GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane427GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 34 ≤ (0 : Int)
        ·
          exact plane427GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 36 ≤ (0 : Int)
          ·
            exact plane427GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane427GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 35 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 47 ≤ (0 : Int)
        ·
          exact plane427GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane427GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane427GenLeaf0012 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 14 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 48 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 35 ≤ (0 : Int)
        ·
          exact plane427GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane427GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane427GenLeaf0015 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 18 ≤ (0 : Int)
      ·
        exact plane427GenLeaf0016 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane427GenLeaf0017 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
