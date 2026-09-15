import FrozenRegistry.Btp224Leaves000
import FrozenRegistry.Btp224Leaves001
import FrozenRegistry.Btp224Leaves002
import FrozenRegistry.Btp224Leaves003
import FrozenRegistry.Btp224Leaves004
import FrozenRegistry.Btp224Leaves005
import FrozenRegistry.Btp224Leaves006
import FrozenRegistry.Btp224Leaves007
import FrozenRegistry.Btp224Leaves008
import FrozenRegistry.Btp224Leaves009
import FrozenRegistry.Btp224Leaves010
import FrozenRegistry.Btp224Leaves011
import FrozenRegistry.Btp224Leaves012
import FrozenRegistry.Btp224Leaves013
import FrozenRegistry.Btp224Leaves014
import FrozenRegistry.Btp224Leaves015
import FrozenRegistry.Btp224Leaves016
import FrozenRegistry.Btp224Leaves017
import FrozenRegistry.Btp224Leaves018
import FrozenRegistry.Btp224Leaves019
import FrozenRegistry.Btp224Leaves020
import FrozenRegistry.Btp224Leaves021
import FrozenRegistry.Btp224Leaves022
import FrozenRegistry.Btp224Leaves023
import FrozenRegistry.Btp224Leaves024
import FrozenRegistry.Btp224Leaves025
import FrozenRegistry.Btp224Leaves026
import FrozenRegistry.Btp224Leaves027
import FrozenRegistry.Btp224Leaves028
import FrozenRegistry.Btp224Leaves029
import FrozenRegistry.Btp224Leaves030
import FrozenRegistry.Btp224Leaves031
import FrozenRegistry.Btp224Leaves032
import FrozenRegistry.Btp224Leaves033
import FrozenRegistry.Btp224Leaves034
import FrozenRegistry.Btp224Leaves035
import FrozenRegistry.Btp224Leaves036
import FrozenRegistry.Btp224Leaves037
import FrozenRegistry.Btp224Leaves038
import FrozenRegistry.Btp224Leaves039
import FrozenRegistry.Btp224Leaves040
import FrozenRegistry.Btp224Leaves041
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane224BtpGenNoModel (x : Fin 15 → Int) (hroot : plane224BtpGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 14 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 13 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 12 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 11 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 10 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 9 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 8 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 7 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 6 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLLLLLLL : x 5 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLLLLLLLL : x 4 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLLLLLLLLL : x 3 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLLLLLLLLL : x 2 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLLLLL : x 1 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLLL : x 0 ≤ (0 : Int)
                              ·
                                exact plane224BtpGenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                              ·
                                exact plane224BtpGenLeaf0001 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLLR : x 1 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane224BtpGenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  exact plane224BtpGenLeaf0003 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLLRR : x 1 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLLRRL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0004 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0005 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0006 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane224BtpGenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  exact plane224BtpGenLeaf0008 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0010 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRLRR : x 1 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLRLRRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0012 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0013 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLRR : x 2 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0015 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRRLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLRRLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0017 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLRRLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0019 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0020 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0021 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0022 x hroot (by omega)
                      ·
                        by_cases hbranch_LLLLLLLLLLR : x 4 ≤ (1 : Int)
                        ·
                          by_cases hbranch_LLLLLLLLLLRL : x 3 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLLRLL : x 2 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLRLLL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLRLLLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane224BtpGenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  exact plane224BtpGenLeaf0024 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLRLLLR : x 1 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRLLLRL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0026 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRLLLRR : x 1 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRLLLRRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0028 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0029 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLLRLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLRLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0031 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRLLRLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRLLRLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0033 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRLLRLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0035 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0036 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLRLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0038 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRLLRRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0040 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0042 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0043 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0044 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0045 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLLLLLLLLRR : x 4 ≤ (2 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLLRRL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLRRLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLRRLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRRLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0046 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0047 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRRLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRRLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0048 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0049 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRRLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0050 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0051 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0052 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLRRLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRRLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRRLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0053 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0054 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRRLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0055 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0056 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0057 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0058 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0059 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLRRLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLRRLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0060 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0061 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0062 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0063 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0064 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0065 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0066 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0067 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0068 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0069 x hroot (by omega)
                    ·
                      exact plane224BtpGenLeaf0070 x hroot (by omega)
                  ·
                    exact plane224BtpGenLeaf0071 x hroot (by omega)
                ·
                  by_cases hbranch_LLLLLLLR : x 7 ≤ (1 : Int)
                  ·
                    by_cases hbranch_LLLLLLLRL : x 6 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLLLLLRLL : x 5 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLLLLLRLLL : x 4 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLLLLRLLLL : x 3 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRLLLLL : x 2 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRLLLLLL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane224BtpGenLeaf0072 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  exact plane224BtpGenLeaf0073 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLLR : x 1 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLLRL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0074 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0075 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLLRR : x 1 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLLRRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0076 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0077 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0078 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLRLLLLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0080 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLRLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0081 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0082 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0083 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0084 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0085 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0086 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0087 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0088 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0089 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0090 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0091 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0092 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0093 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0094 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLLLLLRLLLR : x 4 ≤ (1 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRLLLRL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRLLLRLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLLRLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0095 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0096 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0097 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0098 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0099 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0100 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0101 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRLLLRLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0102 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0103 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0104 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0105 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0106 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0107 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0108 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0109 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0110 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0111 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0112 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0113 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0114 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0115 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0116 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0117 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLLLLLRLLLRR : x 4 ≤ (2 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRLLLRRL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLLRRLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRRLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRRLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0118 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0119 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRRLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0120 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0121 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0122 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0123 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0124 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLRRLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRRLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0125 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0126 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0127 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0128 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0129 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0130 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0131 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLRRLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0132 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0133 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0134 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0135 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0136 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0137 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0138 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0139 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0140 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0141 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0142 x hroot (by omega)
                    ·
                      exact plane224BtpGenLeaf0143 x hroot (by omega)
                  ·
                    by_cases hbranch_LLLLLLLRR : x 7 ≤ (2 : Int)
                    ·
                      by_cases hbranch_LLLLLLLRRL : x 6 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLLLLLRRLL : x 5 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLLLLRRLLL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRRLLLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRRLLLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRRLLLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0144 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0145 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0146 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0147 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0148 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0149 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0150 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0151 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0152 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0153 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0154 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0155 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0156 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0157 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0158 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0159 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0160 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0161 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0162 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0163 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0164 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0165 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0166 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLLLLLRRLLLR : x 4 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRRLLLRL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRRLLLRLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLRLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0167 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0168 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0169 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0170 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0171 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0172 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0173 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLRLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0174 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0175 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0176 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0177 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0178 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0179 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0180 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0181 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0182 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0183 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0184 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0185 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0186 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0187 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0188 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0189 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLRRLLLRR : x 4 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRRLLLRRL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLRRLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRRLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRRLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0190 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0191 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRRLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0192 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0193 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0194 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0195 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0196 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLRRLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRRLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0197 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0198 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0199 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0200 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0201 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0202 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0203 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLRRLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0204 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0205 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0206 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0207 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLLLLLRRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0208 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0209 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0210 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0211 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0212 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0213 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0214 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0215 x hroot (by omega)
                    ·
                      exact plane224BtpGenLeaf0216 x hroot (by omega)
              ·
                exact plane224BtpGenLeaf0217 x hroot (by omega)
            ·
              exact plane224BtpGenLeaf0218 x hroot (by omega)
          ·
            exact plane224BtpGenLeaf0219 x hroot (by omega)
        ·
          by_cases hbranch_LLLR : x 11 ≤ (1 : Int)
          ·
            by_cases hbranch_LLLRL : x 10 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLRLL : x 9 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLRLLL : x 8 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLRLLLL : x 7 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLRLLLLL : x 6 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLRLLLLLL : x 5 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLRLLLLLLL : x 4 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLRLLLLLLLL : x 3 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLLLLLL : x 2 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLLLLLLL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane224BtpGenLeaf0220 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  exact plane224BtpGenLeaf0221 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0222 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0223 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLLRR : x 1 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLLRRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0224 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0225 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0226 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRLLLLLLLLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0227 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0228 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0229 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0230 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLLLRLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0231 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0232 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0233 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0234 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0235 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLLLRRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0236 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0237 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLLLRRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0238 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0239 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0240 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0241 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0242 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLRLLLLLLLR : x 4 ≤ (1 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLLLLRL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLLLLRLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLLRLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0243 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0244 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0245 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0246 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0247 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0248 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0249 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLLLLRLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0250 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0251 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0252 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0253 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0254 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0255 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0256 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0257 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0258 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0259 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0260 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0261 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0262 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0263 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0264 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0265 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRLLLLLLLRR : x 4 ≤ (2 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLLLLRRL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLLRRLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRRLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRRLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0266 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0267 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRRLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRRLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0268 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0269 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRRLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0270 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0271 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0272 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLRRLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRRLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRRLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0273 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0274 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRRLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0275 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0276 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0277 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0278 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0279 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLRRLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLRRLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0280 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0281 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0282 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0283 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0284 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0285 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0286 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0287 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0288 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0289 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0290 x hroot (by omega)
                    ·
                      exact plane224BtpGenLeaf0291 x hroot (by omega)
                  ·
                    by_cases hbranch_LLLRLLLLR : x 7 ≤ (1 : Int)
                    ·
                      by_cases hbranch_LLLRLLLLRL : x 6 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLRLLLLRLL : x 5 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLRLLLLRLLL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLRLLLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRLLLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRLLLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0292 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0293 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0294 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0295 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0296 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0297 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0298 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLRLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0299 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0300 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0301 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0302 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0303 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0304 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0305 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0306 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0307 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0308 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0309 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0310 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0311 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0312 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0313 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0314 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRLLLLRLLLR : x 4 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRLLLRL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRLLLRLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLRLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0315 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0316 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0317 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0318 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0319 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0320 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0321 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLRLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0322 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0323 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0324 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0325 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0326 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0327 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0328 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0329 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0330 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0331 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0332 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0333 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0334 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0335 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0336 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0337 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRLLLLRLLLRR : x 4 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRLLLRRL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLRRLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRRLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRRLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0338 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0339 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRRLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0340 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0341 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0342 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0343 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0344 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLRRLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRRLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0345 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0346 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0347 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0348 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0349 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0350 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0351 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLRRLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0352 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0353 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0354 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0355 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRLLLLRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0356 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0357 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0358 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0359 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0360 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0361 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0362 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0363 x hroot (by omega)
                    ·
                      by_cases hbranch_LLLRLLLLRR : x 7 ≤ (2 : Int)
                      ·
                        by_cases hbranch_LLLRLLLLRRL : x 6 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLRLLLLRRLL : x 5 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLRRLLL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRRLLLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRRLLLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0364 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0365 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0366 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0367 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0368 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0369 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0370 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0371 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0372 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0373 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0374 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0375 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0376 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0377 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0378 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0379 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0380 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0381 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0382 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0383 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0384 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0385 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0386 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRLLLLRRLLLR : x 4 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRRLLLRL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLLRLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLRLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0387 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0388 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0389 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0390 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0391 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0392 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0393 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLRLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0394 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0395 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0396 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0397 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0398 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0399 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0400 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0401 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0402 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0403 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0404 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0405 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0406 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0407 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0408 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0409 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLRRLLLRR : x 4 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLLRRL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLRRLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRRLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRRLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0410 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0411 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRRLLLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0412 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0413 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0414 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0415 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0416 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLRRLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRRLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0417 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0418 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0419 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0420 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0421 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0422 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0423 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLRRLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0424 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0425 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0426 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0427 x hroot (by omega)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                              ·
                                                by_cases hbranch_LLLRLLLLRRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                                ·
                                                  exact plane224BtpGenLeaf0428 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0429 x hroot (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0430 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0431 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0432 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0433 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0434 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0435 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0436 x hroot (by omega)
                ·
                  exact plane224BtpGenLeaf0437 x hroot (by omega)
              ·
                exact plane224BtpGenLeaf0438 x hroot (by omega)
            ·
              exact plane224BtpGenLeaf0439 x hroot (by omega)
          ·
            by_cases hbranch_LLLRR : x 11 ≤ (2 : Int)
            ·
              by_cases hbranch_LLLRRL : x 10 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLRRLL : x 9 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLRRLLL : x 8 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLRRLLLL : x 7 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLRRLLLLL : x 6 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLRRLLLLLL : x 5 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLRRLLLLLLL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRRLLLLLLLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLLLLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLLLLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane224BtpGenLeaf0440 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0441 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0442 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0443 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLLRR : x 1 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLLRRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0444 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0445 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0446 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRRLLLLLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0447 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0448 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0449 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0450 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLLLRLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0451 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0452 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0453 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0454 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0455 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLLLRRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0456 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0457 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLLLRRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0458 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0459 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0460 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0461 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0462 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRRLLLLLLLR : x 4 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLLLLRL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLLLLRLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLRLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0463 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0464 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0465 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0466 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0467 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0468 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0469 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLRLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0470 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0471 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0472 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0473 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0474 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0475 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0476 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0477 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0478 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0479 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0480 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0481 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0482 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0483 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0484 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0485 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRRLLLLLLLRR : x 4 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLLLLRRL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLRRLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRRLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRRLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0486 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0487 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRRLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRRLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0488 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0489 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRRLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0490 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0491 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0492 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLRRLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRRLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRRLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0493 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0494 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRRLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0495 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0496 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0497 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0498 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0499 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLRRLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLRRLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0500 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0501 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0502 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0503 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0504 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0505 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0506 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0507 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0508 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0509 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0510 x hroot (by omega)
                      ·
                        exact plane224BtpGenLeaf0511 x hroot (by omega)
                    ·
                      by_cases hbranch_LLLRRLLLLR : x 7 ≤ (1 : Int)
                      ·
                        by_cases hbranch_LLLRRLLLLRL : x 6 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLRRLLLLRLL : x 5 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRRLLLLRLLL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLRLLLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRLLLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane224BtpGenLeaf0512 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0513 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLLR : x 1 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLLRL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0514 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0515 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLLRR : x 1 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLLRRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0516 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0517 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0518 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0519 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0520 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLRLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0521 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0522 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0523 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0524 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0525 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0526 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0527 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0528 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0529 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0530 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0531 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0532 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0533 x hroot (by omega)
                              ·
                                exact plane224BtpGenLeaf0534 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRRLLLLRLLLR : x 4 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRLLLRL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLLRLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLRLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0535 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0536 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0537 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0538 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0539 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0540 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0541 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLRLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0542 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0543 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0544 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0545 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0546 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0547 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0548 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0549 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0550 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0551 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0552 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0553 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0554 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0555 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0556 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0557 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRRLLLLRLLLRR : x 4 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLLRRL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLRRLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRRLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRRLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0558 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0559 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRRLLLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0560 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0561 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0562 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0563 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0564 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLRRLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRRLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0565 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0566 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0567 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0568 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0569 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0570 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0571 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLRRLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0572 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0573 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0574 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0575 x hroot (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                                ·
                                                  exact plane224BtpGenLeaf0576 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0577 x hroot (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0578 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0579 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0580 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0581 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0582 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0583 x hroot (by omega)
                      ·
                        by_cases hbranch_LLLRRLLLLRR : x 7 ≤ (2 : Int)
                        ·
                          by_cases hbranch_LLLRRLLLLRRL : x 6 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRRLLLLRRLL : x 5 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLRRLLL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRRLLLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRRLLLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane224BtpGenLeaf0584 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0585 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLLR : x 1 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLLRL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0586 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0587 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLLRR : x 1 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLLRRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0588 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0589 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0590 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0591 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0592 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLRLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0593 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0594 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLLLRLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0595 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0596 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0597 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0598 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0599 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLLLRRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0600 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0601 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLLLRRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLLLRRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0602 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0603 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0604 x hroot (by omega)
                                      ·
                                        exact plane224BtpGenLeaf0605 x hroot (by omega)
                                ·
                                  exact plane224BtpGenLeaf0606 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRRLLLLRRLLLR : x 4 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRRLLLRL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLLRLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLRLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane224BtpGenLeaf0607 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0608 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRLLLR : x 1 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRLLLRL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0609 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0610 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRLLLRR : x 1 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRLLLRRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0611 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0612 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0613 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLRLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0614 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0615 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRLLRLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRLLRLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0616 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0617 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRLLRLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRLLRLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0618 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0619 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0620 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0621 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0622 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRLLRRLR : x 1 ≤ (1 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRLLRRLRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0623 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0624 x hroot (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRLLRRLRR : x 1 ≤ (2 : Int)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLLRLLRRLRRL : x 0 ≤ (0 : Int)
                                                ·
                                                  exact plane224BtpGenLeaf0625 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0626 x hroot (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0627 x hroot (by omega)
                                        ·
                                          exact plane224BtpGenLeaf0628 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0629 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLRRLLLRR : x 4 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLLRRL : x 3 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLRRLL : x 2 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRRLLL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRRLLLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane224BtpGenLeaf0630 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0631 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRRLLLR : x 1 ≤ (1 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRRLLLRL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0632 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0633 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRRLLLRR : x 1 ≤ (2 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRRLLLRRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0634 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0635 x hroot (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0636 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLRRLLR : x 2 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRRLLRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRRLLRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane224BtpGenLeaf0637 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane224BtpGenLeaf0638 x hroot (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRRLLRLR : x 1 ≤ (1 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRRLLRLRL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0639 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0640 x hroot (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRRLLRLRR : x 1 ≤ (2 : Int)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLLRRLLRLRRL : x 0 ≤ (0 : Int)
                                                ·
                                                  exact plane224BtpGenLeaf0641 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0642 x hroot (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0643 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLRRLLRR : x 2 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLRRLLRRL : x 1 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRRLLRRLL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane224BtpGenLeaf0644 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane224BtpGenLeaf0645 x hroot (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLRRLLRRLR : x 1 ≤ (1 : Int)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLLRRLLRRLRL : x 0 ≤ (0 : Int)
                                                ·
                                                  exact plane224BtpGenLeaf0646 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0647 x hroot (by omega)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLLRRLLRRLRR : x 1 ≤ (2 : Int)
                                                ·
                                                  by_cases hbranch_LLLRRLLLLRRLLLRRLLRRLRRL : x 0 ≤ (0 : Int)
                                                  ·
                                                    exact plane224BtpGenLeaf0648 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                  ·
                                                    exact plane224BtpGenLeaf0649 x hroot (by omega)
                                                ·
                                                  exact plane224BtpGenLeaf0650 x hroot (by omega)
                                          ·
                                            exact plane224BtpGenLeaf0651 x hroot (by omega)
                                    ·
                                      exact plane224BtpGenLeaf0652 x hroot (by omega)
                                  ·
                                    exact plane224BtpGenLeaf0653 x hroot (by omega)
                            ·
                              exact plane224BtpGenLeaf0654 x hroot (by omega)
                          ·
                            exact plane224BtpGenLeaf0655 x hroot (by omega)
                        ·
                          exact plane224BtpGenLeaf0656 x hroot (by omega)
                  ·
                    exact plane224BtpGenLeaf0657 x hroot (by omega)
                ·
                  exact plane224BtpGenLeaf0658 x hroot (by omega)
              ·
                exact plane224BtpGenLeaf0659 x hroot (by omega)
            ·
              exact plane224BtpGenLeaf0660 x hroot (by omega)
      ·
        exact plane224BtpGenLeaf0661 x hroot (by omega)
    ·
      exact plane224BtpGenLeaf0662 x hroot (by omega)
  ·
    exact plane224BtpGenLeaf0663 x hroot (by omega)

end QiushiMatmul
