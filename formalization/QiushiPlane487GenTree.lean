import QiushiPlane487GenLeaf0000
import QiushiPlane487GenLeaf0001
import QiushiPlane487GenLeaf0002
import QiushiPlane487GenLeaf0003
import QiushiPlane487GenLeaf0004
import QiushiPlane487GenLeaf0005
import QiushiPlane487GenLeaf0006
import QiushiPlane487GenLeaf0007
import QiushiPlane487GenLeaf0008
import QiushiPlane487GenLeaf0009
import QiushiPlane487GenLeaf0010
import QiushiPlane487GenLeaf0011
import QiushiPlane487GenLeaf0012
import QiushiPlane487GenLeaf0013
import QiushiPlane487GenLeaf0014
import QiushiPlane487GenLeaf0015
import QiushiPlane487GenLeaf0016
import QiushiPlane487GenLeaf0017
import QiushiPlane487GenLeaf0018
import QiushiPlane487GenLeaf0019
import QiushiPlane487GenLeaf0020
import QiushiPlane487GenLeaf0021
import QiushiPlane487GenLeaf0022
import QiushiPlane487GenLeaf0023
import QiushiPlane487GenLeaf0024
import QiushiPlane487GenLeaf0025
import QiushiPlane487GenLeaf0026
import QiushiPlane487GenLeaf0027
import QiushiPlane487GenLeaf0028
import QiushiPlane487GenLeaf0029
import QiushiPlane487GenLeaf0030
import QiushiPlane487GenLeaf0031
import QiushiPlane487GenLeaf0032
import QiushiPlane487GenLeaf0033
import QiushiPlane487GenLeaf0034
import QiushiPlane487GenLeaf0035
import QiushiPlane487GenLeaf0036
import QiushiPlane487GenLeaf0037
import QiushiPlane487GenLeaf0038
import QiushiPlane487GenLeaf0039
import QiushiPlane487GenLeaf0040
import QiushiPlane487GenLeaf0041
import QiushiPlane487GenLeaf0042
import QiushiPlane487GenLeaf0043
import QiushiPlane487GenLeaf0044
import QiushiPlane487GenLeaf0045
import QiushiPlane487GenLeaf0046
import QiushiPlane487GenLeaf0047
import QiushiPlane487GenLeaf0048
import QiushiPlane487GenLeaf0049
import QiushiPlane487GenLeaf0050
import QiushiPlane487GenLeaf0051
import QiushiPlane487GenLeaf0052
import QiushiPlane487GenLeaf0053
import QiushiPlane487GenLeaf0054
import QiushiPlane487GenLeaf0055
import QiushiPlane487GenLeaf0056
import QiushiPlane487GenLeaf0057
import QiushiPlane487GenLeaf0058
import QiushiPlane487GenLeaf0059
import QiushiPlane487GenLeaf0060
import QiushiPlane487GenLeaf0061
import QiushiPlane487GenLeaf0062
import QiushiPlane487GenLeaf0063
import QiushiPlane487GenLeaf0064
import QiushiPlane487GenLeaf0065
import QiushiPlane487GenLeaf0066
import QiushiPlane487GenLeaf0067
import QiushiPlane487GenLeaf0068
import QiushiPlane487GenLeaf0069
import QiushiPlane487GenLeaf0070
import QiushiPlane487GenLeaf0071
import QiushiPlane487GenLeaf0072
import QiushiPlane487GenLeaf0073
import QiushiPlane487GenLeaf0074
import QiushiPlane487GenLeaf0075
import QiushiPlane487GenLeaf0076
import QiushiPlane487GenLeaf0077
import QiushiPlane487GenLeaf0078
import QiushiPlane487GenLeaf0079
import QiushiPlane487GenLeaf0080
import QiushiPlane487GenLeaf0081
import QiushiPlane487GenLeaf0082
import QiushiPlane487GenLeaf0083
import QiushiPlane487GenLeaf0084
import QiushiPlane487GenLeaf0085
import QiushiPlane487GenLeaf0086
import QiushiPlane487GenLeaf0087
import QiushiPlane487GenLeaf0088
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane487GenNoModel (x : Fin 48 → Int) (hroot : plane487GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 39 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 23 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 6 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 25 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 12 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 15 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 16 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 38 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 9 ≤ (0 : Int)
                  ·
                    exact plane487GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    by_cases hbranch_LLLLLLLLR : x 33 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLLLLLLRL : x 19 ≤ (0 : Int)
                      ·
                        exact plane487GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane487GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane487GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLLLLR : x 14 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLRL : x 33 ≤ (0 : Int)
                  ·
                    exact plane487GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLLR : x 40 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLLR : x 3 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLRL : x 24 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLRLL : x 36 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLRLLL : x 17 ≤ (0 : Int)
                  ·
                    exact plane487GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLRR : x 26 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 1 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 35 ≤ (0 : Int)
            ·
              exact plane487GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLRR : x 35 ≤ (0 : Int)
            ·
              exact plane487GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 33 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 14 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 29 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLLL : x 9 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLRLLLR : x 44 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLRLLLRL : x 25 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLRLLLRLL : x 22 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLRLLLRLLL : x 41 ≤ (0 : Int)
                      ·
                        exact plane487GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane487GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane487GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRLLR : x 3 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLLRL : x 12 ≤ (0 : Int)
                ·
                  exact plane487GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRLR : x 24 ≤ (0 : Int)
            ·
              exact plane487GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 12 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRRL : x 42 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRRLL : x 36 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRRLLL : x 19 ≤ (0 : Int)
                ·
                  exact plane487GenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRRR : x 19 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRRRL : x 17 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRRRR : x 22 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 2 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 4 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 46 ≤ (0 : Int)
          ·
            exact plane487GenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0040 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRLR : x 10 ≤ (0 : Int)
          ·
            exact plane487GenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 6 ≤ (0 : Int)
        ·
          by_cases hbranch_LRRL : x 12 ≤ (0 : Int)
          ·
            by_cases hbranch_LRRLL : x 14 ≤ (0 : Int)
            ·
              exact plane487GenLeaf0043 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0044 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0045 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane487GenLeaf0046 x hroot (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 7 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 28 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 40 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 29 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLLL : x 19 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLLL : x 36 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLLLL : x 23 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLLLLLLL : x 45 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLLLLLL : x 5 ≤ (0 : Int)
                    ·
                      by_cases hbranch_RLLLLLLLLL : x 25 ≤ (0 : Int)
                      ·
                        by_cases hbranch_RLLLLLLLLLL : x 30 ≤ (0 : Int)
                        ·
                          by_cases hbranch_RLLLLLLLLLLL : x 2 ≤ (0 : Int)
                          ·
                            exact plane487GenLeaf0047 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                          ·
                            by_cases hbranch_RLLLLLLLLLLLR : x 21 ≤ (0 : Int)
                            ·
                              exact plane487GenLeaf0048 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                            ·
                              exact plane487GenLeaf0049 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                        ·
                          exact plane487GenLeaf0050 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane487GenLeaf0051 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      by_cases hbranch_RLLLLLLLLR : x 1 ≤ (0 : Int)
                      ·
                        exact plane487GenLeaf0052 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        by_cases hbranch_RLLLLLLLLRR : x 26 ≤ (0 : Int)
                        ·
                          exact plane487GenLeaf0053 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                        ·
                          exact plane487GenLeaf0054 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    by_cases hbranch_RLLLLLLLR : x 10 ≤ (0 : Int)
                    ·
                      exact plane487GenLeaf0055 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane487GenLeaf0056 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hbranch_RLLLLLLR : x 10 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLLLLRL : x 16 ≤ (0 : Int)
                    ·
                      by_cases hbranch_RLLLLLLRLL : x 20 ≤ (0 : Int)
                      ·
                        by_cases hbranch_RLLLLLLRLLL : x 33 ≤ (0 : Int)
                        ·
                          exact plane487GenLeaf0057 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                        ·
                          exact plane487GenLeaf0058 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane487GenLeaf0059 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane487GenLeaf0060 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0061 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_RLLLLLR : x 37 ≤ (0 : Int)
                ·
                  exact plane487GenLeaf0062 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0063 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RLLLLR : x 17 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLLRL : x 4 ≤ (0 : Int)
                ·
                  exact plane487GenLeaf0064 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0065 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0066 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLLLR : x 10 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLRL : x 12 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLRLL : x 16 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLLLRLLL : x 20 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLRLLLL : x 11 ≤ (0 : Int)
                    ·
                      exact plane487GenLeaf0067 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane487GenLeaf0068 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0069 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane487GenLeaf0070 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0071 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0072 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLLR : x 13 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLRL : x 32 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLRLL : x 33 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0073 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0074 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0075 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0076 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 3 ≤ (0 : Int)
        ·
          by_cases hbranch_RLRL : x 36 ≤ (0 : Int)
          ·
            by_cases hbranch_RLRLL : x 35 ≤ (0 : Int)
            ·
              by_cases hbranch_RLRLLL : x 13 ≤ (0 : Int)
              ·
                by_cases hbranch_RLRLLLL : x 37 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLRLLLLL : x 38 ≤ (0 : Int)
                  ·
                    exact plane487GenLeaf0077 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0078 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hbranch_RLRLLLLR : x 9 ≤ (0 : Int)
                  ·
                    exact plane487GenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane487GenLeaf0080 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0081 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RLRLLR : x 19 ≤ (0 : Int)
              ·
                exact plane487GenLeaf0082 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane487GenLeaf0083 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0084 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLRR : x 37 ≤ (0 : Int)
          ·
            by_cases hbranch_RLRRL : x 17 ≤ (0 : Int)
            ·
              exact plane487GenLeaf0085 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane487GenLeaf0086 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane487GenLeaf0087 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      exact plane487GenLeaf0088 x hroot (by omega) (by omega)

end QiushiMatmul
