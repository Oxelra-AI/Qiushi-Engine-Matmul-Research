import FrozenRegistry.Btp227Leaves000
import FrozenRegistry.Btp227Leaves001
import FrozenRegistry.Btp227Leaves002
import FrozenRegistry.Btp227Leaves003
import FrozenRegistry.Btp227Leaves004
import FrozenRegistry.Btp227Leaves005
import FrozenRegistry.Btp227Leaves006
import FrozenRegistry.Btp227Leaves007
import FrozenRegistry.Btp227Leaves008
import FrozenRegistry.Btp227Leaves009
import FrozenRegistry.Btp227Leaves010
import FrozenRegistry.Btp227Leaves011
import FrozenRegistry.Btp227Leaves012
import FrozenRegistry.Btp227Leaves013
import FrozenRegistry.Btp227Leaves014
import FrozenRegistry.Btp227Leaves015
import FrozenRegistry.Btp227Leaves016
import FrozenRegistry.Btp227Leaves017
import FrozenRegistry.Btp227Leaves018
import FrozenRegistry.Btp227Leaves019
import FrozenRegistry.Btp227Leaves020
import FrozenRegistry.Btp227Leaves021
import FrozenRegistry.Btp227Leaves022
import FrozenRegistry.Btp227Leaves023
import FrozenRegistry.Btp227Leaves024
import FrozenRegistry.Btp227Leaves025
import FrozenRegistry.Btp227Leaves026
import FrozenRegistry.Btp227Leaves027
import FrozenRegistry.Btp227Leaves028
import FrozenRegistry.Btp227Leaves029
import FrozenRegistry.Btp227Leaves030
import FrozenRegistry.Btp227Leaves031
import FrozenRegistry.Btp227Leaves032
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane227BtpGenNoModel (x : Fin 15 → Int) (hroot : plane227BtpGenOccSys.RootHolds x) : False := by
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
                                exact plane227BtpGenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                ·
                                  exact plane227BtpGenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0003 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0004 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane227BtpGenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0008 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0009 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLRR : x 2 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0010 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLRRLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0013 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0014 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0015 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0016 x hroot (by omega)
                      ·
                        exact plane227BtpGenLeaf0017 x hroot (by omega)
                    ·
                      by_cases hbranch_LLLLLLLLLR : x 5 ≤ (1 : Int)
                      ·
                        by_cases hbranch_LLLLLLLLLRL : x 4 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLLLLLLRLL : x 3 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLRLLL : x 2 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLRLLLL : x 1 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                ·
                                  exact plane227BtpGenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0021 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0022 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLRLLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0023 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0024 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0026 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0027 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLRLLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLRLLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRLLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0029 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0031 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0032 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0033 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0034 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0035 x hroot (by omega)
                      ·
                        by_cases hbranch_LLLLLLLLLRR : x 5 ≤ (2 : Int)
                        ·
                          by_cases hbranch_LLLLLLLLLRRL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLRRLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLRRLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLRRLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLRRLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRRLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0039 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0040 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLLLRRLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLRRLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRRLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0043 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0044 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0045 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLLLRRLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLRRLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0046 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0047 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0048 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0049 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0050 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0051 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0052 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0053 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0054 x hroot (by omega)
                  ·
                    exact plane227BtpGenLeaf0055 x hroot (by omega)
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
                                  exact plane227BtpGenLeaf0056 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLLLR : x 0 ≤ (1 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0057 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLLLRR : x 0 ≤ (2 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0058 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0059 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0060 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLRLLLLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0061 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0062 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0063 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0064 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0065 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0066 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0067 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0068 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0069 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0070 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0071 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0072 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0073 x hroot (by omega)
                      ·
                        by_cases hbranch_LLLLLLLRLLR : x 5 ≤ (1 : Int)
                        ·
                          by_cases hbranch_LLLLLLLRLLRL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRLLRLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRLLRLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLRLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLRLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0074 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0075 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0076 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0077 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0078 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRLLRLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLRLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0080 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0081 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0082 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0083 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLRLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0084 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0085 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0086 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0087 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0088 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0089 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0090 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0091 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLLLLLRLLRR : x 5 ≤ (2 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRLLRRL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRLLRRLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRLLRRLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRLLRRLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRRLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0092 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0093 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0094 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0095 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0096 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRLLRRLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRRLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0097 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0098 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0099 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0100 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0101 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRLLRRLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0102 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0103 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLLLLLRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0104 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0105 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0106 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0107 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0108 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0109 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0110 x hroot (by omega)
                    ·
                      exact plane227BtpGenLeaf0111 x hroot (by omega)
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
                                    exact plane227BtpGenLeaf0112 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0113 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0114 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0115 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0116 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0117 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0118 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0119 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0120 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0121 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0122 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0123 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0124 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0125 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0126 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0127 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0128 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0129 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLLLLLRRLLR : x 5 ≤ (1 : Int)
                          ·
                            by_cases hbranch_LLLLLLLRRLLRL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRRLLRLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRRLLRLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLRLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLRLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0130 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0131 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0132 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0133 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0134 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLRLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLRLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0135 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0136 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0137 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0138 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0139 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLRLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0140 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0141 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0142 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0143 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0144 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0145 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0146 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0147 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLLLLLRRLLRR : x 5 ≤ (2 : Int)
                            ·
                              by_cases hbranch_LLLLLLLRRLLRRL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLRRLLRRLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLRRLLRRLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLRRLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRRLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0148 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0149 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0150 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0151 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0152 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLLLLLRRLLRRLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRRLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0153 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0154 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0155 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0156 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0157 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLLLLLRRLLRRLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLRRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLRRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0158 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLLLLLRRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0159 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLLLLLRRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0160 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0161 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0162 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0163 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0164 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0165 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0166 x hroot (by omega)
                      ·
                        exact plane227BtpGenLeaf0167 x hroot (by omega)
                    ·
                      exact plane227BtpGenLeaf0168 x hroot (by omega)
              ·
                exact plane227BtpGenLeaf0169 x hroot (by omega)
            ·
              exact plane227BtpGenLeaf0170 x hroot (by omega)
          ·
            exact plane227BtpGenLeaf0171 x hroot (by omega)
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
                                  exact plane227BtpGenLeaf0172 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0173 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0174 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0175 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0176 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRLLLLLLLLLR : x 2 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0177 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0178 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0179 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0180 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0181 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLLLLLLRR : x 2 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0182 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLLLLRRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0183 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0184 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0185 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0186 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0187 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0188 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0189 x hroot (by omega)
                      ·
                        by_cases hbranch_LLLRLLLLLLR : x 5 ≤ (1 : Int)
                        ·
                          by_cases hbranch_LLLRLLLLLLRL : x 4 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLLLRLL : x 3 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLLLRLLL : x 2 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                  ·
                                    exact plane227BtpGenLeaf0190 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0191 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0192 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0193 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0194 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0195 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0196 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0197 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0198 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0199 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLRLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0200 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0201 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0202 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0203 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0204 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0205 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0206 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0207 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLRLLLLLLRR : x 5 ≤ (2 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLLLRRL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLLLRRLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLLLRRLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLLLRRLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRRLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0208 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRRLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0209 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0210 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0211 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0212 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLLLRRLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRRLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRRLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0213 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0214 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0215 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0216 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0217 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLLLRRLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLLLRRLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0218 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0219 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0220 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0221 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0222 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0223 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0224 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0225 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0226 x hroot (by omega)
                    ·
                      exact plane227BtpGenLeaf0227 x hroot (by omega)
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
                                    exact plane227BtpGenLeaf0228 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0229 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0230 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0231 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0232 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRLLLLRLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0233 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0234 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0235 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0236 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0237 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0238 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0239 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0240 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0241 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0242 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0243 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0244 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0245 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLRLLLLRLLR : x 5 ≤ (1 : Int)
                          ·
                            by_cases hbranch_LLLRLLLLRLLRL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRLLRLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRLLRLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLRLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLRLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0246 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0247 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0248 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0249 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0250 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLRLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLRLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0251 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0252 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0253 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0254 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0255 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLRLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0256 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0257 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0258 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0259 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0260 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0261 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0262 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0263 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRLLLLRLLRR : x 5 ≤ (2 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRLLRRL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRLLRRLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRLLRRLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLRRLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRRLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0264 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0265 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0266 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0267 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0268 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRLLRRLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRRLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0269 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0270 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0271 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0272 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0273 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRLLRRLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0274 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0275 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRLLLLRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0276 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0277 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0278 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0279 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0280 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0281 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0282 x hroot (by omega)
                      ·
                        exact plane227BtpGenLeaf0283 x hroot (by omega)
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
                                      exact plane227BtpGenLeaf0284 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0285 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0286 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0287 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0288 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0289 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0290 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0291 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0292 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0293 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0294 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0295 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0296 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0297 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0298 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0299 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0300 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0301 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRLLLLRRLLR : x 5 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLRLLLLRRLLRL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRRLLRLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLRLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLRLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLRLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0302 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0303 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0304 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0305 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0306 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLRLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLRLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0307 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0308 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0309 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0310 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0311 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLRLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0312 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0313 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0314 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0315 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0316 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0317 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0318 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0319 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRLLLLRRLLRR : x 5 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLRLLLLRRLLRRL : x 4 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRLLLLRRLLRRLL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRLLLLRRLLRRLLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLRRLLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRRLLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0320 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0321 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0322 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0323 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0324 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRLLLLRRLLRRLLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRRLLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0325 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0326 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0327 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0328 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0329 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRLLLLRRLLRRLLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRLLLLRRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRLLLLRRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0330 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRLLLLRRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0331 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                by_cases hbranch_LLLRLLLLRRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                                ·
                                                  exact plane227BtpGenLeaf0332 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane227BtpGenLeaf0333 x hroot (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0334 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0335 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0336 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0337 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0338 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0339 x hroot (by omega)
                      ·
                        exact plane227BtpGenLeaf0340 x hroot (by omega)
                ·
                  exact plane227BtpGenLeaf0341 x hroot (by omega)
              ·
                exact plane227BtpGenLeaf0342 x hroot (by omega)
            ·
              exact plane227BtpGenLeaf0343 x hroot (by omega)
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
                                    exact plane227BtpGenLeaf0344 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0345 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0346 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0347 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0348 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRRLLLLLLLLLR : x 2 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0349 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0350 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0351 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0352 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0353 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLLLLRR : x 2 ≤ (2 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLLLLRRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLLLLRRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0354 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLLLLRRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0355 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0356 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0357 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0358 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0359 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0360 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0361 x hroot (by omega)
                        ·
                          by_cases hbranch_LLLRRLLLLLLR : x 5 ≤ (1 : Int)
                          ·
                            by_cases hbranch_LLLRRLLLLLLRL : x 4 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLLLRLL : x 3 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLLLRLLL : x 2 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                    ·
                                      exact plane227BtpGenLeaf0362 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0363 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0364 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0365 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0366 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0367 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0368 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0369 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0370 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0371 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLRLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0372 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0373 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0374 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0375 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0376 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0377 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0378 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0379 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRRLLLLLLRR : x 5 ≤ (2 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLLLRRL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLLLRRLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLLLRRLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLRRLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRRLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0380 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRRLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0381 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0382 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0383 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0384 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLLLRRLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRRLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRRLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0385 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0386 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0387 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0388 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0389 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLLLRRLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLLLRRLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0390 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0391 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0392 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0393 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0394 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0395 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0396 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0397 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0398 x hroot (by omega)
                      ·
                        exact plane227BtpGenLeaf0399 x hroot (by omega)
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
                                      exact plane227BtpGenLeaf0400 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLLLR : x 0 ≤ (1 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0401 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLLLRR : x 0 ≤ (2 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0402 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0403 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0404 x hroot (by omega)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLLLLR : x 2 ≤ (1 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLRL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLRLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0405 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0406 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0407 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0408 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0409 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLLLLRR : x 2 ≤ (2 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLLLLRRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLLLLRRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0410 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0411 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0412 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0413 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0414 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0415 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0416 x hroot (by omega)
                            ·
                              exact plane227BtpGenLeaf0417 x hroot (by omega)
                          ·
                            by_cases hbranch_LLLRRLLLLRLLR : x 5 ≤ (1 : Int)
                            ·
                              by_cases hbranch_LLLRRLLLLRLLRL : x 4 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRLLRLL : x 3 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLRLLL : x 2 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLRLLLL : x 1 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLRLLLLL : x 0 ≤ (0 : Int)
                                      ·
                                        exact plane227BtpGenLeaf0418 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0419 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0420 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0421 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0422 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLRLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLRLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0423 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0424 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0425 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0426 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0427 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLRLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0428 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0429 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0430 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0431 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0432 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0433 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0434 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0435 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRRLLLLRLLRR : x 5 ≤ (2 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRLLRRL : x 4 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRLLRRLL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRLLRRLLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLRRLLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRRLLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0436 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0437 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0438 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0439 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0440 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRLLRRLLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRRLLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0441 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0442 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0443 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0444 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0445 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRLLRRLLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0446 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0447 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                                ·
                                                  exact plane227BtpGenLeaf0448 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane227BtpGenLeaf0449 x hroot (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0450 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0451 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0452 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0453 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0454 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0455 x hroot (by omega)
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
                                        exact plane227BtpGenLeaf0456 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLLLR : x 0 ≤ (1 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0457 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLLLRR : x 0 ≤ (2 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0458 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0459 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0460 x hroot (by omega)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLLLLR : x 2 ≤ (1 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLRL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLRLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0461 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0462 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLLLRLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0463 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0464 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0465 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLLLLRR : x 2 ≤ (2 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLLLLRRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLLLLRRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0466 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLLLLRRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0467 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLLLLRRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0468 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0469 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0470 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0471 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0472 x hroot (by omega)
                              ·
                                exact plane227BtpGenLeaf0473 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLRRLLLLRRLLR : x 5 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLRRLLLLRRLLRL : x 4 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRRLLRLL : x 3 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLRLLL : x 2 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLRLLLL : x 1 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLRLLLLL : x 0 ≤ (0 : Int)
                                        ·
                                          exact plane227BtpGenLeaf0474 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRLLLLLR : x 0 ≤ (1 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0475 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRLLLLLRR : x 0 ≤ (2 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0476 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0477 x hroot (by omega)
                                      ·
                                        exact plane227BtpGenLeaf0478 x hroot (by omega)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLRLLLR : x 2 ≤ (1 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLRLLLRL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRLLLRLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0479 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRLLLRLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0480 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0481 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0482 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0483 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLRLLLRR : x 2 ≤ (2 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRLLLRRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRLLLRRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0484 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLRLLLRRLLR : x 0 ≤ (1 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0485 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLRLLLRRLLRR : x 0 ≤ (2 : Int)
                                                ·
                                                  exact plane227BtpGenLeaf0486 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane227BtpGenLeaf0487 x hroot (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0488 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0489 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0490 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0491 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLRRLLLLRRLLRR : x 5 ≤ (2 : Int)
                                ·
                                  by_cases hbranch_LLLRRLLLLRRLLRRL : x 4 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLRRLLLLRRLLRRLL : x 3 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLRRLLLLRRLLRRLLL : x 2 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLRRLLLL : x 1 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRRLLLLL : x 0 ≤ (0 : Int)
                                          ·
                                            exact plane227BtpGenLeaf0492 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRRLLLLLR : x 0 ≤ (1 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0493 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLRRLLLLLRR : x 0 ≤ (2 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0494 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                exact plane227BtpGenLeaf0495 x hroot (by omega)
                                        ·
                                          exact plane227BtpGenLeaf0496 x hroot (by omega)
                                      ·
                                        by_cases hbranch_LLLRRLLLLRRLLRRLLLR : x 2 ≤ (1 : Int)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRRLLLRL : x 1 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRRLLLRLL : x 0 ≤ (0 : Int)
                                            ·
                                              exact plane227BtpGenLeaf0497 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLRRLLLRLLR : x 0 ≤ (1 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0498 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLRRLLLRLLRR : x 0 ≤ (2 : Int)
                                                ·
                                                  exact plane227BtpGenLeaf0499 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  exact plane227BtpGenLeaf0500 x hroot (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0501 x hroot (by omega)
                                        ·
                                          by_cases hbranch_LLLRRLLLLRRLLRRLLLRR : x 2 ≤ (2 : Int)
                                          ·
                                            by_cases hbranch_LLLRRLLLLRRLLRRLLLRRL : x 1 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLRRLLLLRRLLRRLLLRRLL : x 0 ≤ (0 : Int)
                                              ·
                                                exact plane227BtpGenLeaf0502 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                              ·
                                                by_cases hbranch_LLLRRLLLLRRLLRRLLLRRLLR : x 0 ≤ (1 : Int)
                                                ·
                                                  exact plane227BtpGenLeaf0503 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                ·
                                                  by_cases hbranch_LLLRRLLLLRRLLRRLLLRRLLRR : x 0 ≤ (2 : Int)
                                                  ·
                                                    exact plane227BtpGenLeaf0504 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                  ·
                                                    exact plane227BtpGenLeaf0505 x hroot (by omega)
                                            ·
                                              exact plane227BtpGenLeaf0506 x hroot (by omega)
                                          ·
                                            exact plane227BtpGenLeaf0507 x hroot (by omega)
                                    ·
                                      exact plane227BtpGenLeaf0508 x hroot (by omega)
                                  ·
                                    exact plane227BtpGenLeaf0509 x hroot (by omega)
                                ·
                                  exact plane227BtpGenLeaf0510 x hroot (by omega)
                          ·
                            exact plane227BtpGenLeaf0511 x hroot (by omega)
                        ·
                          exact plane227BtpGenLeaf0512 x hroot (by omega)
                  ·
                    exact plane227BtpGenLeaf0513 x hroot (by omega)
                ·
                  exact plane227BtpGenLeaf0514 x hroot (by omega)
              ·
                exact plane227BtpGenLeaf0515 x hroot (by omega)
            ·
              exact plane227BtpGenLeaf0516 x hroot (by omega)
      ·
        exact plane227BtpGenLeaf0517 x hroot (by omega)
    ·
      exact plane227BtpGenLeaf0518 x hroot (by omega)
  ·
    exact plane227BtpGenLeaf0519 x hroot (by omega)

end QiushiMatmul
