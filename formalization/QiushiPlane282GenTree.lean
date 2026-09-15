import QiushiPlane282GenLeaf0000
import QiushiPlane282GenLeaf0001
import QiushiPlane282GenLeaf0002
import QiushiPlane282GenLeaf0003
import QiushiPlane282GenLeaf0004
import QiushiPlane282GenLeaf0005
import QiushiPlane282GenLeaf0006
import QiushiPlane282GenLeaf0007
import QiushiPlane282GenLeaf0008
import QiushiPlane282GenLeaf0009
import QiushiPlane282GenLeaf0010
import QiushiPlane282GenLeaf0011
import QiushiPlane282GenLeaf0012
import QiushiPlane282GenLeaf0013
import QiushiPlane282GenLeaf0014
import QiushiPlane282GenLeaf0015
import QiushiPlane282GenLeaf0016
import QiushiPlane282GenLeaf0017
import QiushiPlane282GenLeaf0018
import QiushiPlane282GenLeaf0019
import QiushiPlane282GenLeaf0020
import QiushiPlane282GenLeaf0021
import QiushiPlane282GenLeaf0022
import QiushiPlane282GenLeaf0023
import QiushiPlane282GenLeaf0024
import QiushiPlane282GenLeaf0025
import QiushiPlane282GenLeaf0026
import QiushiPlane282GenLeaf0027
import QiushiPlane282GenLeaf0028
import QiushiPlane282GenLeaf0029
import QiushiPlane282GenLeaf0030
import QiushiPlane282GenLeaf0031
import QiushiPlane282GenLeaf0032
import QiushiPlane282GenLeaf0033
import QiushiPlane282GenLeaf0034
import QiushiPlane282GenLeaf0035
import QiushiPlane282GenLeaf0036
import QiushiPlane282GenLeaf0037
import QiushiPlane282GenLeaf0038
import QiushiPlane282GenLeaf0039
import QiushiPlane282GenLeaf0040
import QiushiPlane282GenLeaf0041
import QiushiPlane282GenLeaf0042
import QiushiPlane282GenLeaf0043
import QiushiPlane282GenLeaf0044
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane282GenNoModel (x : Fin 28 → Int) (hroot : plane282GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 12 ≤ (0 : Int)
  ·
    by_cases hL : x 4 ≤ (0 : Int)
    ·
      exact plane282GenLeaf0000 x hroot (by omega) (by omega)
    ·
      by_cases hLR : x 18 ≤ (0 : Int)
      ·
        by_cases hLRL : x 19 ≤ (0 : Int)
        ·
          by_cases hLRLL : x 22 ≤ (1 : Int)
          ·
            by_cases hLRLLL : x 25 ≤ (0 : Int)
            ·
              by_cases hLRLLLL : x 1 ≤ (0 : Int)
              ·
                by_cases hLRLLLLL : x 0 ≤ (3 : Int)
                ·
                  by_cases hLRLLLLLL : x 9 ≤ (0 : Int)
                  ·
                    exact plane282GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    by_cases hLRLLLLLLR : x 2 ≤ (1 : Int)
                    ·
                      exact plane282GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane282GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane282GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hLRLLLLR : x 6 ≤ (1 : Int)
                ·
                  exact plane282GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hLRLLLLRR : x 26 ≤ (0 : Int)
                  ·
                    by_cases hLRLLLLRRL : x 2 ≤ (1 : Int)
                    ·
                      exact plane282GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane282GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane282GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hLRLLLR : x 0 ≤ (2 : Int)
              ·
                exact plane282GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hLRLLLRR : x 8 ≤ (1 : Int)
                ·
                  exact plane282GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane282GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hLRLLR : x 8 ≤ (1 : Int)
            ·
              by_cases hLRLLRL : x 0 ≤ (2 : Int)
              ·
                exact plane282GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hLRLLRLR : x 1 ≤ (0 : Int)
                ·
                  by_cases hLRLLRLRL : x 26 ≤ (0 : Int)
                  ·
                    by_cases hLRLLRLRLL : x 2 ≤ (1 : Int)
                    ·
                      by_cases hLRLLRLRLLL : x 6 ≤ (1 : Int)
                      ·
                        exact plane282GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane282GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      by_cases hLRLLRLRLLR : x 4 ≤ (1 : Int)
                      ·
                        exact plane282GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane282GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane282GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hLRLLRLRR : x 2 ≤ (1 : Int)
                  ·
                    exact plane282GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane282GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hLRLLRR : x 4 ≤ (1 : Int)
              ·
                by_cases hLRLLRRL : x 9 ≤ (0 : Int)
                ·
                  exact plane282GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane282GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane282GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hLRLR : x 14 ≤ (0 : Int)
          ·
            by_cases hLRLRL : x 0 ≤ (2 : Int)
            ·
              exact plane282GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane282GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane282GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hLRR : x 19 ≤ (0 : Int)
        ·
          by_cases hLRRL : x 11 ≤ (0 : Int)
          ·
            by_cases hLRRLL : x 4 ≤ (1 : Int)
            ·
              exact plane282GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane282GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane282GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hLRRR : x 0 ≤ (2 : Int)
          ·
            exact plane282GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane282GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hR : x 8 ≤ (1 : Int)
    ·
      by_cases hRL : x 2 ≤ (1 : Int)
      ·
        by_cases hRLL : x 22 ≤ (1 : Int)
        ·
          by_cases hRLLL : x 16 ≤ (0 : Int)
          ·
            by_cases hRLLLL : x 19 ≤ (0 : Int)
            ·
              exact plane282GenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane282GenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hRLLLR : x 1 ≤ (0 : Int)
            ·
              exact plane282GenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane282GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane282GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hRLR : x 0 ≤ (2 : Int)
        ·
          exact plane282GenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hRLRR : x 1 ≤ (0 : Int)
          ·
            by_cases hRLRRL : x 9 ≤ (0 : Int)
            ·
              by_cases hRLRRLL : x 10 ≤ (0 : Int)
              ·
                exact plane282GenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane282GenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane282GenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane282GenLeaf0040 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hRR : x 24 ≤ (0 : Int)
      ·
        by_cases hRRL : x 9 ≤ (0 : Int)
        ·
          by_cases hRRLL : x 4 ≤ (1 : Int)
          ·
            exact plane282GenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane282GenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane282GenLeaf0043 x hroot (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane282GenLeaf0044 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
