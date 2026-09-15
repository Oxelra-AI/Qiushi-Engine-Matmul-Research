import QiushiPlane490GenLeaf0000
import QiushiPlane490GenLeaf0001
import QiushiPlane490GenLeaf0002
import QiushiPlane490GenLeaf0003
import QiushiPlane490GenLeaf0004
import QiushiPlane490GenLeaf0005
import QiushiPlane490GenLeaf0006
import QiushiPlane490GenLeaf0007
import QiushiPlane490GenLeaf0008
import QiushiPlane490GenLeaf0009
import QiushiPlane490GenLeaf0010
import QiushiPlane490GenLeaf0011
import QiushiPlane490GenLeaf0012
import QiushiPlane490GenLeaf0013
import QiushiPlane490GenLeaf0014
import QiushiPlane490GenLeaf0015
import QiushiPlane490GenLeaf0016
import QiushiPlane490GenLeaf0017
import QiushiPlane490GenLeaf0018
import QiushiPlane490GenLeaf0019
import QiushiPlane490GenLeaf0020
import QiushiPlane490GenLeaf0021
import QiushiPlane490GenLeaf0022
import QiushiPlane490GenLeaf0023
import QiushiPlane490GenLeaf0024
import QiushiPlane490GenLeaf0025
import QiushiPlane490GenLeaf0026
import QiushiPlane490GenLeaf0027
import QiushiPlane490GenLeaf0028
import QiushiPlane490GenLeaf0029
import QiushiPlane490GenLeaf0030
import QiushiPlane490GenLeaf0031
import QiushiPlane490GenLeaf0032
import QiushiPlane490GenLeaf0033
import QiushiPlane490GenLeaf0034
import QiushiPlane490GenLeaf0035
import QiushiPlane490GenLeaf0036
import QiushiPlane490GenLeaf0037
import QiushiPlane490GenLeaf0038
import QiushiPlane490GenLeaf0039
import QiushiPlane490GenLeaf0040
import QiushiPlane490GenLeaf0041
import QiushiPlane490GenLeaf0042
import QiushiPlane490GenLeaf0043
import QiushiPlane490GenLeaf0044
import QiushiPlane490GenLeaf0045
import QiushiPlane490GenLeaf0046
import QiushiPlane490GenLeaf0047
import QiushiPlane490GenLeaf0048
import QiushiPlane490GenLeaf0049
import QiushiPlane490GenLeaf0050
import QiushiPlane490GenLeaf0051
import QiushiPlane490GenLeaf0052
import QiushiPlane490GenLeaf0053
import QiushiPlane490GenLeaf0054
import QiushiPlane490GenLeaf0055
import QiushiPlane490GenLeaf0056
import QiushiPlane490GenLeaf0057
import QiushiPlane490GenLeaf0058
import QiushiPlane490GenLeaf0059
import QiushiPlane490GenLeaf0060
import QiushiPlane490GenLeaf0061
import QiushiPlane490GenLeaf0062
import QiushiPlane490GenLeaf0063
import QiushiPlane490GenLeaf0064
import QiushiPlane490GenLeaf0065
import QiushiPlane490GenLeaf0066
import QiushiPlane490GenLeaf0067
import QiushiPlane490GenLeaf0068
import QiushiPlane490GenLeaf0069
import QiushiPlane490GenLeaf0070
import QiushiPlane490GenLeaf0071
import QiushiPlane490GenLeaf0072
import QiushiPlane490GenLeaf0073
import QiushiPlane490GenLeaf0074
import QiushiPlane490GenLeaf0075
import QiushiPlane490GenLeaf0076
import QiushiPlane490GenLeaf0077
import QiushiPlane490GenLeaf0078
import QiushiPlane490GenLeaf0079
import QiushiPlane490GenLeaf0080
import QiushiPlane490GenLeaf0081
import QiushiPlane490GenLeaf0082
import QiushiPlane490GenLeaf0083
import QiushiPlane490GenLeaf0084
import QiushiPlane490GenLeaf0085
import QiushiPlane490GenLeaf0086
import QiushiPlane490GenLeaf0087
import QiushiPlane490GenLeaf0088
import QiushiPlane490GenLeaf0089
import QiushiPlane490GenLeaf0090
import QiushiPlane490GenLeaf0091
import QiushiPlane490GenLeaf0092
import QiushiPlane490GenLeaf0093
import QiushiPlane490GenLeaf0094
import QiushiPlane490GenLeaf0095
import QiushiPlane490GenLeaf0096
import QiushiPlane490GenLeaf0097
import QiushiPlane490GenLeaf0098
import QiushiPlane490GenLeaf0099
import QiushiPlane490GenLeaf0100
import QiushiPlane490GenLeaf0101
import QiushiPlane490GenLeaf0102
import QiushiPlane490GenLeaf0103
import QiushiPlane490GenLeaf0104
import QiushiPlane490GenLeaf0105
import QiushiPlane490GenLeaf0106
import QiushiPlane490GenLeaf0107
import QiushiPlane490GenLeaf0108
import QiushiPlane490GenLeaf0109
import QiushiPlane490GenLeaf0110
import QiushiPlane490GenLeaf0111
import QiushiPlane490GenLeaf0112
import QiushiPlane490GenLeaf0113
import QiushiPlane490GenLeaf0114
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane490GenNoModel (x : Fin 43 → Int) (hroot : plane490GenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 29 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 4 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 23 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 16 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 39 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 19 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 10 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 30 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 12 ≤ (0 : Int)
                  ·
                    exact plane490GenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLLLLR : x 27 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLLR : x 30 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLRL : x 25 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLLR : x 17 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLRL : x 22 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLRLL : x 20 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLRLLL : x 42 ≤ (0 : Int)
                  ·
                    exact plane490GenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLLRLR : x 30 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLLRR : x 8 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 15 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLRL : x 21 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRLL : x 32 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLLRR : x 32 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRRL : x 3 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLRRLL : x 42 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLRRLLL : x 20 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLRRLLLL : x 38 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0021 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLLRRLR : x 33 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0022 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLLRRR : x 20 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLRRRL : x 33 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LLR : x 30 ≤ (0 : Int)
        ·
          by_cases hbranch_LLRL : x 28 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRLL : x 35 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLLL : x 5 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLLLL : x 38 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLRLLLLL : x 25 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLRLLLLLL : x 15 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLRLLLLLLL : x 24 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLRLLLLLLLL : x 26 ≤ (0 : Int)
                        ·
                          exact plane490GenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                        ·
                          exact plane490GenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane490GenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      by_cases hbranch_LLRLLLLLLR : x 3 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLRLLLLLLRL : x 14 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLRLLLLLLRLL : x 24 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLRLLLLLLRLLL : x 42 ≤ (0 : Int)
                            ·
                              exact plane490GenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                            ·
                              exact plane490GenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                          ·
                            exact plane490GenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                        ·
                          exact plane490GenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      ·
                        exact plane490GenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0035 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLRLLLR : x 19 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLRLLLRL : x 39 ≤ (0 : Int)
                  ·
                    exact plane490GenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    by_cases hbranch_LLRLLLRLR : x 16 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0040 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRLLR : x 42 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLLRL : x 15 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLRLLRLL : x 36 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLRLLRLLL : x 3 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0043 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hbranch_LLRLLRLR : x 0 ≤ (0 : Int)
                  ·
                    exact plane490GenLeaf0044 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0045 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0046 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRLR : x 39 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRLRL : x 21 ≤ (0 : Int)
              ·
                by_cases hbranch_LLRLRLL : x 33 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLRLRLLL : x 14 ≤ (0 : Int)
                  ·
                    exact plane490GenLeaf0047 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0048 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0049 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0050 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LLRLRR : x 19 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0051 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0052 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLRR : x 6 ≤ (0 : Int)
          ·
            by_cases hbranch_LLRRL : x 10 ≤ (0 : Int)
            ·
              exact plane490GenLeaf0053 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0054 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LLRRR : x 22 ≤ (0 : Int)
            ·
              by_cases hbranch_LLRRRL : x 39 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0055 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_LLRRRLR : x 31 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0056 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0057 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0058 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 34 ≤ (0 : Int)
      ·
        by_cases hbranch_LRL : x 23 ≤ (0 : Int)
        ·
          by_cases hbranch_LRLL : x 39 ≤ (0 : Int)
          ·
            exact plane490GenLeaf0059 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLLR : x 18 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLLRL : x 15 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0060 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0061 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_LRLLRR : x 40 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0062 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0063 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRLR : x 25 ≤ (0 : Int)
          ·
            by_cases hbranch_LRLRL : x 18 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLRLL : x 21 ≤ (0 : Int)
              ·
                by_cases hbranch_LRLRLLL : x 11 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0064 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0065 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0066 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0067 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_LRLRR : x 33 ≤ (0 : Int)
            ·
              by_cases hbranch_LRLRRL : x 5 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0068 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0069 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0070 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_LRR : x 3 ≤ (0 : Int)
        ·
          by_cases hbranch_LRRL : x 40 ≤ (0 : Int)
          ·
            by_cases hbranch_LRRLL : x 14 ≤ (0 : Int)
            ·
              exact plane490GenLeaf0071 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0072 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane490GenLeaf0073 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LRRR : x 1 ≤ (0 : Int)
          ·
            exact plane490GenLeaf0074 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane490GenLeaf0075 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 18 ≤ (0 : Int)
    ·
      by_cases hbranch_RL : x 12 ≤ (0 : Int)
      ·
        by_cases hbranch_RLL : x 22 ≤ (0 : Int)
        ·
          by_cases hbranch_RLLL : x 1 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLLL : x 10 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLLL : x 14 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLLLL : x 9 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0076 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0077 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0078 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RLLLR : x 42 ≤ (0 : Int)
            ·
              by_cases hbranch_RLLLRL : x 32 ≤ (0 : Int)
              ·
                by_cases hbranch_RLLLRLL : x 8 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLLLRLLL : x 16 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLRLLLL : x 2 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0080 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0081 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0082 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  by_cases hbranch_RLLLRLLR : x 23 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLRLLRL : x 10 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0083 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0084 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0085 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_RLLLRLR : x 2 ≤ (0 : Int)
                ·
                  by_cases hbranch_RLLLRLRL : x 34 ≤ (0 : Int)
                  ·
                    by_cases hbranch_RLLLRLRLL : x 37 ≤ (0 : Int)
                    ·
                      exact plane490GenLeaf0086 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    ·
                      exact plane490GenLeaf0087 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  ·
                    exact plane490GenLeaf0088 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0089 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0090 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RLLR : x 3 ≤ (0 : Int)
          ·
            by_cases hbranch_RLLRL : x 2 ≤ (0 : Int)
            ·
              exact plane490GenLeaf0091 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0092 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane490GenLeaf0093 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RLR : x 2 ≤ (0 : Int)
        ·
          exact plane490GenLeaf0094 x hroot (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane490GenLeaf0095 x hroot (by omega) (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 14 ≤ (0 : Int)
      ·
        by_cases hbranch_RRL : x 1 ≤ (0 : Int)
        ·
          by_cases hbranch_RRLL : x 21 ≤ (0 : Int)
          ·
            by_cases hbranch_RRLLL : x 3 ≤ (0 : Int)
            ·
              by_cases hbranch_RRLLLL : x 20 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0096 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0097 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0098 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RRLLR : x 8 ≤ (0 : Int)
            ·
              exact plane490GenLeaf0099 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0100 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RRLR : x 20 ≤ (0 : Int)
          ·
            by_cases hbranch_RRLRL : x 15 ≤ (0 : Int)
            ·
              by_cases hbranch_RRLRLL : x 12 ≤ (0 : Int)
              ·
                by_cases hbranch_RRLRLLL : x 33 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0101 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0102 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0103 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RRLRLR : x 31 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0104 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0105 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            by_cases hbranch_RRLRR : x 8 ≤ (0 : Int)
            ·
              by_cases hbranch_RRLRRL : x 2 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0106 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                exact plane490GenLeaf0107 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              by_cases hbranch_RRLRRR : x 0 ≤ (0 : Int)
              ·
                exact plane490GenLeaf0108 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              ·
                by_cases hbranch_RRLRRRR : x 16 ≤ (0 : Int)
                ·
                  exact plane490GenLeaf0109 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                ·
                  exact plane490GenLeaf0110 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RRR : x 32 ≤ (0 : Int)
        ·
          by_cases hbranch_RRRL : x 38 ≤ (0 : Int)
          ·
            by_cases hbranch_RRRLL : x 25 ≤ (0 : Int)
            ·
              exact plane490GenLeaf0111 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane490GenLeaf0112 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane490GenLeaf0113 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          exact plane490GenLeaf0114 x hroot (by omega) (by omega) (by omega) (by omega)

end QiushiMatmul
