import FrozenRegistry.Btp260Leaves000
import FrozenRegistry.Btp260Leaves001
import FrozenRegistry.Btp260Leaves002
import FrozenRegistry.Btp260Leaves003
import FrozenRegistry.Btp260Leaves004
import FrozenRegistry.Btp260Leaves005
import FrozenRegistry.Btp260Leaves006
import FrozenRegistry.Btp260Leaves007
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane260BtpGenNoModel (x : Fin 31 → Int) (hroot : plane260BtpGenOccSys.RootHolds x) : False := by
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
                                                                exact plane260BtpGenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 0 ≤ (1 : Int)
                                                                ·
                                                                  exact plane260BtpGenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLRR : x 0 ≤ (2 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0003 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0004 x hroot (by omega)
                                                          ·
                                                            exact plane260BtpGenLeaf0005 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLR : x 3 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLRL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLRLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLRLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane260BtpGenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLRLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLLRLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0009 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0010 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0011 x hroot (by omega)
                                                          ·
                                                            exact plane260BtpGenLeaf0012 x hroot (by omega)
                                                      ·
                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLR : x 4 ≤ (1 : Int)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRL : x 3 ≤ (0 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLL : x 2 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLLL : x 1 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLLLL : x 0 ≤ (0 : Int)
                                                                ·
                                                                  exact plane260BtpGenLeaf0013 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0014 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0015 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0016 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0017 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0018 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 3 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLRL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLRLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLRLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0019 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLLRLRLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0020 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0021 x hroot (by omega) (by omega) (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0022 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0023 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0024 x hroot (by omega)
                                                        ·
                                                          exact plane260BtpGenLeaf0025 x hroot (by omega)
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
                                                                  exact plane260BtpGenLeaf0026 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0027 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0028 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0029 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0030 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0031 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLR : x 3 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLRL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLRLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLRLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0032 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLRLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0033 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLLRLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0034 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0035 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0036 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0037 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0038 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLR : x 4 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0039 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0040 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0041 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0042 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0043 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0044 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLR : x 3 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLRL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLRLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLRLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0045 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLLRLRLRLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0046 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0047 x hroot (by omega) (by omega) (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0048 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0049 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0050 x hroot (by omega)
                                                          ·
                                                            exact plane260BtpGenLeaf0051 x hroot (by omega)
                                                      ·
                                                        exact plane260BtpGenLeaf0052 x hroot (by omega)
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
                                                                  exact plane260BtpGenLeaf0053 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLLR : x 0 ≤ (1 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0054 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLLLLRR : x 0 ≤ (2 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0055 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0056 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0057 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0058 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLR : x 3 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLRL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLRLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0059 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0060 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLLRLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0061 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0062 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0063 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0064 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0065 x hroot (by omega)
                                                        ·
                                                          by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLR : x 4 ≤ (1 : Int)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRL : x 3 ≤ (0 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLL : x 2 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLLL : x 1 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLLLL : x 0 ≤ (0 : Int)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0066 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0067 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLLLLRR : x 0 ≤ (2 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0068 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0069 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0070 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0071 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLR : x 3 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLRL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLRLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLRLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0072 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLLRLRLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0073 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0074 x hroot (by omega) (by omega) (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0075 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0076 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0077 x hroot (by omega)
                                                          ·
                                                            exact plane260BtpGenLeaf0078 x hroot (by omega)
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
                                                                    exact plane260BtpGenLeaf0079 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLLLLR : x 0 ≤ (1 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0080 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0081 x hroot (by omega) (by omega) (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0082 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0083 x hroot (by omega)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLR : x 3 ≤ (1 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLRL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLRLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLRLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0084 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLLRLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0085 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0086 x hroot (by omega) (by omega) (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0087 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0088 x hroot (by omega)
                                                              ·
                                                                exact plane260BtpGenLeaf0089 x hroot (by omega)
                                                          ·
                                                            by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLR : x 4 ≤ (1 : Int)
                                                            ·
                                                              by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRL : x 3 ≤ (0 : Int)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLL : x 2 ≤ (0 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLLL : x 1 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLLLL : x 0 ≤ (0 : Int)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0090 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLLLLR : x 0 ≤ (1 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0091 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0092 x hroot (by omega) (by omega) (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0093 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0094 x hroot (by omega)
                                                              ·
                                                                by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLR : x 3 ≤ (1 : Int)
                                                                ·
                                                                  by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLRL : x 2 ≤ (0 : Int)
                                                                  ·
                                                                    by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLRLL : x 1 ≤ (0 : Int)
                                                                    ·
                                                                      by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLRLLL : x 0 ≤ (0 : Int)
                                                                      ·
                                                                        exact plane260BtpGenLeaf0095 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                      ·
                                                                        by_cases hbranch_LLLLLLLLLLLLLLLLLLLLLLLLRLRLRLRLLLR : x 0 ≤ (1 : Int)
                                                                        ·
                                                                          exact plane260BtpGenLeaf0096 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                                                        ·
                                                                          exact plane260BtpGenLeaf0097 x hroot (by omega) (by omega) (by omega)
                                                                    ·
                                                                      exact plane260BtpGenLeaf0098 x hroot (by omega)
                                                                  ·
                                                                    exact plane260BtpGenLeaf0099 x hroot (by omega)
                                                                ·
                                                                  exact plane260BtpGenLeaf0100 x hroot (by omega)
                                                            ·
                                                              exact plane260BtpGenLeaf0101 x hroot (by omega)
                                                        ·
                                                          exact plane260BtpGenLeaf0102 x hroot (by omega)
                                                    ·
                                                      exact plane260BtpGenLeaf0103 x hroot (by omega)
                                                ·
                                                  exact plane260BtpGenLeaf0104 x hroot (by omega)
                                              ·
                                                exact plane260BtpGenLeaf0105 x hroot (by omega)
                                            ·
                                              exact plane260BtpGenLeaf0106 x hroot (by omega)
                                          ·
                                            exact plane260BtpGenLeaf0107 x hroot (by omega)
                                        ·
                                          exact plane260BtpGenLeaf0108 x hroot (by omega)
                                      ·
                                        exact plane260BtpGenLeaf0109 x hroot (by omega)
                                    ·
                                      exact plane260BtpGenLeaf0110 x hroot (by omega)
                                  ·
                                    exact plane260BtpGenLeaf0111 x hroot (by omega)
                                ·
                                  exact plane260BtpGenLeaf0112 x hroot (by omega)
                              ·
                                exact plane260BtpGenLeaf0113 x hroot (by omega)
                            ·
                              exact plane260BtpGenLeaf0114 x hroot (by omega)
                          ·
                            exact plane260BtpGenLeaf0115 x hroot (by omega)
                        ·
                          exact plane260BtpGenLeaf0116 x hroot (by omega)
                      ·
                        exact plane260BtpGenLeaf0117 x hroot (by omega)
                    ·
                      exact plane260BtpGenLeaf0118 x hroot (by omega)
                  ·
                    exact plane260BtpGenLeaf0119 x hroot (by omega)
                ·
                  exact plane260BtpGenLeaf0120 x hroot (by omega)
              ·
                exact plane260BtpGenLeaf0121 x hroot (by omega)
            ·
              exact plane260BtpGenLeaf0122 x hroot (by omega)
          ·
            exact plane260BtpGenLeaf0123 x hroot (by omega)
        ·
          exact plane260BtpGenLeaf0124 x hroot (by omega)
      ·
        exact plane260BtpGenLeaf0125 x hroot (by omega)
    ·
      exact plane260BtpGenLeaf0126 x hroot (by omega)
  ·
    exact plane260BtpGenLeaf0127 x hroot (by omega)

end QiushiMatmul
