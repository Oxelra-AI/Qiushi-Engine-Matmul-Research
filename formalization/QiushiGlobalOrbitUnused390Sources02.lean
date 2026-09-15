import QiushiGlobalOrbitUnused390Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane390UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [129, 68, 36, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(129, 272), (68, 168), (36, 45), (20, 44), (8, 2), (2, 32)]
    (codeMat 266) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_262_row11_qr

theorem plane390UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [259, 135, 68, 32, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(259, 364), (135, 268), (68, 269), (32, 504), (20, 280), (10, 31)]
    (codeMat 117) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane390UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 39, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(259, 371), (128, 504), (68, 269), (39, 30), (20, 21), (10, 31)]
    (codeMat 403) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane390UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 118), (160, 413), (64, 384), (16, 360), (9, 256), (4, 9), (3, 8)]
    (codeMat 249) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane390UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 434), (129, 76), (66, 77), (32, 16), (18, 256), (10, 264), (6, 432)]
    (codeMat 213) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane390UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 79), (128, 1), (66, 77), (33, 168), (18, 8), (10, 264), (6, 432)]
    (codeMat 156) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
