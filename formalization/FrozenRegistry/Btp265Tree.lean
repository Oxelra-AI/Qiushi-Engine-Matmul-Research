import FrozenRegistry.Btp265Leaves000
import FrozenRegistry.Btp265Leaves001
import FrozenRegistry.Btp265Leaves002
import FrozenRegistry.Btp265Leaves003
import FrozenRegistry.Btp265Leaves004
import FrozenRegistry.Btp265Leaves005
import FrozenRegistry.Btp265Leaves006
import FrozenRegistry.Btp265Leaves007
import FrozenRegistry.Btp265Leaves008
import FrozenRegistry.Btp265Leaves009
import FrozenRegistry.Btp265Leaves010
import FrozenRegistry.Btp265Leaves011
import FrozenRegistry.Btp265Leaves012
import FrozenRegistry.Btp265Leaves013
import FrozenRegistry.Btp265Leaves014
import FrozenRegistry.Btp265Leaves015
import FrozenRegistry.Btp265Leaves016
import FrozenRegistry.Btp265Leaves017
import FrozenRegistry.Btp265Leaves018
import FrozenRegistry.Btp265Leaves019
import FrozenRegistry.Btp265Leaves020
import FrozenRegistry.Btp265Leaves021
import FrozenRegistry.Btp265Leaves022
import FrozenRegistry.Btp265Leaves023
import FrozenRegistry.Btp265Leaves024
import FrozenRegistry.Btp265Leaves025
import FrozenRegistry.Btp265Leaves026
import FrozenRegistry.Btp265Leaves027
import FrozenRegistry.Btp265Leaves028
import FrozenRegistry.Btp265Leaves029
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane265BtpGenNoModel (x : Fin 31 → Int) (hroot : plane265BtpGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 30 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 29 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 28 ≤ (0 : Int)
      ·
        by_cases hbranch_LLL : x 27 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 26 ≤ (0 : Int)
          ·
            by_cases hbranch_LLLLL : x 25 ≤ (0 : Int)
            ·
              by_cases hbranch_LLLLLL : x 24 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLLLL : x 23 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLLLLL : x 22 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLLLLLLL : x 21 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLLLLLLLL : x 20 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLLLLLLLLL : x 19 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLLLLLLLLL : x 18 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLLLLLLLLLL : x 17 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLLL : x 16 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLLLL : x 15 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLLLLL : x 14 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLLLLLL : x 13 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLLLLLLLLL : x 12 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLL : x 11 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLL : x 10 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLL : x 9 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLL : x 8 ≤ (0 : Int)
                                              ·
                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLL : x 7 ≤ (0 : Int)
                                                ·
                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLL : x 6 ≤ (0 : Int)
                                                  ·
                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLL : x 5 ≤ (0 : Int)
                                                    ·
                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLL : x 4 ≤ (0 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLL : x 3 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLL : x 2 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLL : x 1 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                                              ·
                                                                exact plane265BtpGenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0004 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0009 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0010 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0011 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0012 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0015 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0016 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0017 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0018 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0020 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0021 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0022 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0023 x hroot (by omega)
                                                      ·
                                                        exact plane265BtpGenLeaf0024 x hroot (by omega)
                                                    ·
                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLR : x 5 ≤ (1 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRL : x 4 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLL : x 3 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0025 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0029 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLR : x 1 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLRL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0030 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0031 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0034 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0035 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0036 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0037 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0038 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0040 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0042 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0043 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0044 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0045 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0046 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0047 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0048 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0049 x hroot (by omega)
                                                      ·
                                                        exact plane265BtpGenLeaf0050 x hroot (by omega)
                                                  ·
                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLR : x 6 ≤ (1 : Int)
                                                    ·
                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRL : x 5 ≤ (0 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLL : x 4 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLL : x 3 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0051 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0052 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0053 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0054 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0055 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLR : x 1 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0056 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0057 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0058 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0059 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0060 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0061 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLR : x 2 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0062 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0063 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0064 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0065 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0066 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0067 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0068 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0069 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0070 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0071 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0072 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0073 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0074 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0075 x hroot (by omega)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLR : x 5 ≤ (1 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0076 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0077 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0078 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0080 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0081 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0082 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0083 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0084 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0085 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0086 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0087 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0088 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0089 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0090 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0091 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0092 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0093 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0094 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0095 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0096 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0097 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0098 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0099 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0100 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0101 x hroot (by omega)
                                                    ·
                                                      exact plane265BtpGenLeaf0102 x hroot (by omega)
                                                ·
                                                  exact plane265BtpGenLeaf0103 x hroot (by omega)
                                              ·
                                                exact plane265BtpGenLeaf0104 x hroot (by omega)
                                            ·
                                              exact plane265BtpGenLeaf0105 x hroot (by omega)
                                          ·
                                            exact plane265BtpGenLeaf0106 x hroot (by omega)
                                        ·
                                          exact plane265BtpGenLeaf0107 x hroot (by omega)
                                      ·
                                        exact plane265BtpGenLeaf0108 x hroot (by omega)
                                    ·
                                      exact plane265BtpGenLeaf0109 x hroot (by omega)
                                  ·
                                    exact plane265BtpGenLeaf0110 x hroot (by omega)
                                ·
                                  exact plane265BtpGenLeaf0111 x hroot (by omega)
                              ·
                                exact plane265BtpGenLeaf0112 x hroot (by omega)
                            ·
                              by_cases hbranch_LLLLLLLLLLLLLR : x 17 ≤ (1 : Int)
                              ·
                                by_cases hbranch_LLLLLLLLLLLLLRL : x 16 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLLLLLLLLLLRLL : x 15 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLLLLLLLLLLRLLL : x 14 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLLLLLLLLLLRLLLL : x 13 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLL : x 12 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLL : x 11 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLL : x 10 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLL : x 9 ≤ (0 : Int)
                                              ·
                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLL : x 8 ≤ (0 : Int)
                                                ·
                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLL : x 7 ≤ (0 : Int)
                                                  ·
                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLL : x 6 ≤ (0 : Int)
                                                    ·
                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLL : x 5 ≤ (0 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLL : x 4 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLL : x 3 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0113 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0114 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0115 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0116 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0117 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0118 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLRLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0119 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0120 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0121 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0122 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0123 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0124 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0125 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0126 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0127 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0128 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0129 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0130 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0131 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0132 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0133 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0134 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0135 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0136 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0137 x hroot (by omega)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLR : x 5 ≤ (1 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0138 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0139 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0140 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0141 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0142 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0143 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0144 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0145 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0146 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0147 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0148 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0149 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0150 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0151 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0152 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0153 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0154 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0155 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0156 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0157 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0158 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0159 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0160 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0161 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0162 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0163 x hroot (by omega)
                                                    ·
                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLR : x 6 ≤ (1 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRL : x 5 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0164 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0165 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0166 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0167 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0168 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0169 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0170 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0171 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0172 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0173 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0174 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0175 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0176 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0177 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0178 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0179 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0180 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0181 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0182 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0183 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0184 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0185 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0186 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0187 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0188 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLR : x 5 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRL : x 4 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLL : x 3 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0189 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0190 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0191 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0192 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0193 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0194 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0195 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0196 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0197 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0198 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0199 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLR : x 2 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0200 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0201 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0202 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0203 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0204 x hroot (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLR : x 1 ≤ (1 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0205 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0206 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0207 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0208 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0209 x hroot (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0210 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0211 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0212 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0213 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0214 x hroot (by omega)
                                                      ·
                                                        exact plane265BtpGenLeaf0215 x hroot (by omega)
                                                  ·
                                                    exact plane265BtpGenLeaf0216 x hroot (by omega)
                                                ·
                                                  exact plane265BtpGenLeaf0217 x hroot (by omega)
                                              ·
                                                exact plane265BtpGenLeaf0218 x hroot (by omega)
                                            ·
                                              exact plane265BtpGenLeaf0219 x hroot (by omega)
                                          ·
                                            exact plane265BtpGenLeaf0220 x hroot (by omega)
                                        ·
                                          exact plane265BtpGenLeaf0221 x hroot (by omega)
                                      ·
                                        exact plane265BtpGenLeaf0222 x hroot (by omega)
                                    ·
                                      exact plane265BtpGenLeaf0223 x hroot (by omega)
                                  ·
                                    exact plane265BtpGenLeaf0224 x hroot (by omega)
                                ·
                                  exact plane265BtpGenLeaf0225 x hroot (by omega)
                              ·
                                exact plane265BtpGenLeaf0226 x hroot (by omega)
                          ·
                            exact plane265BtpGenLeaf0227 x hroot (by omega)
                        ·
                          exact plane265BtpGenLeaf0228 x hroot (by omega)
                      ·
                        exact plane265BtpGenLeaf0229 x hroot (by omega)
                    ·
                      exact plane265BtpGenLeaf0230 x hroot (by omega)
                  ·
                    exact plane265BtpGenLeaf0231 x hroot (by omega)
                ·
                  exact plane265BtpGenLeaf0232 x hroot (by omega)
              ·
                exact plane265BtpGenLeaf0233 x hroot (by omega)
            ·
              exact plane265BtpGenLeaf0234 x hroot (by omega)
          ·
            by_cases hbranch_LLLLR : x 26 ≤ (1 : Int)
            ·
              by_cases hbranch_LLLLRL : x 25 ≤ (0 : Int)
              ·
                by_cases hbranch_LLLLRLL : x 24 ≤ (0 : Int)
                ·
                  by_cases hbranch_LLLLRLLL : x 23 ≤ (0 : Int)
                  ·
                    by_cases hbranch_LLLLRLLLL : x 22 ≤ (0 : Int)
                    ·
                      by_cases hbranch_LLLLRLLLLL : x 21 ≤ (0 : Int)
                      ·
                        by_cases hbranch_LLLLRLLLLLL : x 20 ≤ (0 : Int)
                        ·
                          by_cases hbranch_LLLLRLLLLLLL : x 19 ≤ (0 : Int)
                          ·
                            by_cases hbranch_LLLLRLLLLLLLL : x 18 ≤ (0 : Int)
                            ·
                              by_cases hbranch_LLLLRLLLLLLLLL : x 17 ≤ (0 : Int)
                              ·
                                by_cases hbranch_LLLLRLLLLLLLLLL : x 16 ≤ (0 : Int)
                                ·
                                  by_cases hbranch_LLLLRLLLLLLLLLLL : x 15 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLRLLLLLLLLLLLL : x 14 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLRLLLLLLLLLLLLL : x 13 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLL : x 12 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLL : x 11 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLL : x 10 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLL : x 9 ≤ (0 : Int)
                                              ·
                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLL : x 8 ≤ (0 : Int)
                                                ·
                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLL : x 7 ≤ (0 : Int)
                                                  ·
                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLL : x 6 ≤ (0 : Int)
                                                    ·
                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLL : x 5 ≤ (0 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLL : x 4 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLL : x 3 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane265BtpGenLeaf0235 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0236 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0237 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0238 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0239 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0240 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0241 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0242 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0243 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0244 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0245 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0246 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0247 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0248 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0249 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0250 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0251 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0252 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0253 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0254 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0255 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0256 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0257 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0258 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0259 x hroot (by omega)
                                                      ·
                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLR : x 5 ≤ (1 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0260 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0261 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0262 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0263 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0264 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0265 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0266 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0267 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0268 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0269 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0270 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0271 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0272 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0273 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0274 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0275 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0276 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0277 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0278 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0279 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0280 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0281 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0282 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0283 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0284 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0285 x hroot (by omega)
                                                    ·
                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLR : x 6 ≤ (1 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRL : x 5 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0286 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0287 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0288 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0289 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0290 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0291 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0292 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0293 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0294 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0295 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0296 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0297 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0298 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0299 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0300 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0301 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0302 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0303 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0304 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0305 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0306 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0307 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0308 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0309 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0310 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLR : x 5 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRL : x 4 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLL : x 3 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0311 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0312 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0313 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0314 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0315 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0316 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0317 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0318 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0319 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0320 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0321 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLR : x 2 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0322 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0323 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0324 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0325 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0326 x hroot (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLR : x 1 ≤ (1 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0327 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0328 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0329 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLLLLLLLLLLLLRLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0330 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0331 x hroot (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0332 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0333 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0334 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0335 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0336 x hroot (by omega)
                                                      ·
                                                        exact plane265BtpGenLeaf0337 x hroot (by omega)
                                                  ·
                                                    exact plane265BtpGenLeaf0338 x hroot (by omega)
                                                ·
                                                  exact plane265BtpGenLeaf0339 x hroot (by omega)
                                              ·
                                                exact plane265BtpGenLeaf0340 x hroot (by omega)
                                            ·
                                              exact plane265BtpGenLeaf0341 x hroot (by omega)
                                          ·
                                            exact plane265BtpGenLeaf0342 x hroot (by omega)
                                        ·
                                          exact plane265BtpGenLeaf0343 x hroot (by omega)
                                      ·
                                        exact plane265BtpGenLeaf0344 x hroot (by omega)
                                    ·
                                      exact plane265BtpGenLeaf0345 x hroot (by omega)
                                  ·
                                    exact plane265BtpGenLeaf0346 x hroot (by omega)
                                ·
                                  exact plane265BtpGenLeaf0347 x hroot (by omega)
                              ·
                                by_cases hbranch_LLLLRLLLLLLLLLR : x 17 ≤ (1 : Int)
                                ·
                                  by_cases hbranch_LLLLRLLLLLLLLLRL : x 16 ≤ (0 : Int)
                                  ·
                                    by_cases hbranch_LLLLRLLLLLLLLLRLL : x 15 ≤ (0 : Int)
                                    ·
                                      by_cases hbranch_LLLLRLLLLLLLLLRLLL : x 14 ≤ (0 : Int)
                                      ·
                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLL : x 13 ≤ (0 : Int)
                                        ·
                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLL : x 12 ≤ (0 : Int)
                                          ·
                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLL : x 11 ≤ (0 : Int)
                                            ·
                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLL : x 10 ≤ (0 : Int)
                                              ·
                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLL : x 9 ≤ (0 : Int)
                                                ·
                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLL : x 8 ≤ (0 : Int)
                                                  ·
                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLL : x 7 ≤ (0 : Int)
                                                    ·
                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLL : x 6 ≤ (0 : Int)
                                                      ·
                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLL : x 5 ≤ (0 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLL : x 4 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0348 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0349 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0350 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0351 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0352 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLR : x 1 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLRL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0353 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLRLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0354 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0355 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0356 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0357 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0358 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLR : x 2 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0359 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0360 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0361 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0362 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0363 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0364 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0365 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0366 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0367 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0368 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0369 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0370 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0371 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0372 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLR : x 5 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRL : x 4 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLL : x 3 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0373 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0374 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0375 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0376 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0377 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0378 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0379 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0380 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0381 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0382 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0383 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLR : x 2 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0384 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0385 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0386 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0387 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0388 x hroot (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLR : x 1 ≤ (1 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0389 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0390 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0391 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0392 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0393 x hroot (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0394 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0395 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0396 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0397 x hroot (by omega)
                                                          ·
                                                            exact plane265BtpGenLeaf0398 x hroot (by omega)
                                                      ·
                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLR : x 6 ≤ (1 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRL : x 5 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLL : x 4 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLL : x 3 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0399 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0400 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLLRR : x 0 ≤ (2 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0401 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLLRRR : x 0 ≤ (3 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0402 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0403 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLR : x 1 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLRL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0404 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLRLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0405 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLRLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0406 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0407 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0408 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0409 x hroot (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLR : x 2 ≤ (1 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0410 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0411 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0412 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0413 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0414 x hroot (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLR : x 1 ≤ (1 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLRL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0415 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0416 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0417 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0418 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0419 x hroot (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0420 x hroot (by omega)
                                                                  ·
                                                                    exact plane265BtpGenLeaf0421 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0422 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0423 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLR : x 5 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRL : x 4 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLL : x 3 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLL : x 2 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0424 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0425 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0426 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLLRRR : x 0 ≤ (3 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0427 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0428 x hroot (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLR : x 1 ≤ (1 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLRL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0429 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0430 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0431 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLLRLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0432 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0433 x hroot (by omega)
                                                                      ·
                                                                        exact plane265BtpGenLeaf0434 x hroot (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLR : x 2 ≤ (1 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRL : x 1 ≤ (0 : Int)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLL : x 0 ≤ (0 : Int)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0435 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLR : x 0 ≤ (1 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0436 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLRR : x 0 ≤ (2 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0437 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLLRRR : x 0 ≤ (3 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0438 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0439 x hroot (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLR : x 1 ≤ (1 : Int)
                                                                        ·
                                                                          by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRL : x 0 ≤ (0 : Int)
                                                                          ·
                                                                            exact plane265BtpGenLeaf0440 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                          ·
                                                                            by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLR : x 0 ≤ (1 : Int)
                                                                            ·
                                                                              exact plane265BtpGenLeaf0441 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                            ·
                                                                              by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLRR : x 0 ≤ (2 : Int)
                                                                              ·
                                                                                exact plane265BtpGenLeaf0442 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                              ·
                                                                                by_cases hbranch_LLLLRLLLLLLLLLRLLLLLLLLLLLRLRLLLRLRLRRR : x 0 ≤ (3 : Int)
                                                                                ·
                                                                                  exact plane265BtpGenLeaf0443 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                                ·
                                                                                  exact plane265BtpGenLeaf0444 x hroot (by omega)
                                                                        ·
                                                                          exact plane265BtpGenLeaf0445 x hroot (by omega)
                                                                    ·
                                                                      exact plane265BtpGenLeaf0446 x hroot (by omega)
                                                                ·
                                                                  exact plane265BtpGenLeaf0447 x hroot (by omega)
                                                              ·
                                                                exact plane265BtpGenLeaf0448 x hroot (by omega)
                                                            ·
                                                              exact plane265BtpGenLeaf0449 x hroot (by omega)
                                                        ·
                                                          exact plane265BtpGenLeaf0450 x hroot (by omega)
                                                    ·
                                                      exact plane265BtpGenLeaf0451 x hroot (by omega)
                                                  ·
                                                    exact plane265BtpGenLeaf0452 x hroot (by omega)
                                                ·
                                                  exact plane265BtpGenLeaf0453 x hroot (by omega)
                                              ·
                                                exact plane265BtpGenLeaf0454 x hroot (by omega)
                                            ·
                                              exact plane265BtpGenLeaf0455 x hroot (by omega)
                                          ·
                                            exact plane265BtpGenLeaf0456 x hroot (by omega)
                                        ·
                                          exact plane265BtpGenLeaf0457 x hroot (by omega)
                                      ·
                                        exact plane265BtpGenLeaf0458 x hroot (by omega)
                                    ·
                                      exact plane265BtpGenLeaf0459 x hroot (by omega)
                                  ·
                                    exact plane265BtpGenLeaf0460 x hroot (by omega)
                                ·
                                  exact plane265BtpGenLeaf0461 x hroot (by omega)
                            ·
                              exact plane265BtpGenLeaf0462 x hroot (by omega)
                          ·
                            exact plane265BtpGenLeaf0463 x hroot (by omega)
                        ·
                          exact plane265BtpGenLeaf0464 x hroot (by omega)
                      ·
                        exact plane265BtpGenLeaf0465 x hroot (by omega)
                    ·
                      exact plane265BtpGenLeaf0466 x hroot (by omega)
                  ·
                    exact plane265BtpGenLeaf0467 x hroot (by omega)
                ·
                  exact plane265BtpGenLeaf0468 x hroot (by omega)
              ·
                exact plane265BtpGenLeaf0469 x hroot (by omega)
            ·
              exact plane265BtpGenLeaf0470 x hroot (by omega)
        ·
          exact plane265BtpGenLeaf0471 x hroot (by omega)
      ·
        exact plane265BtpGenLeaf0472 x hroot (by omega)
    ·
      exact plane265BtpGenLeaf0473 x hroot (by omega)
  ·
    exact plane265BtpGenLeaf0474 x hroot (by omega)

end QiushiMatmul
