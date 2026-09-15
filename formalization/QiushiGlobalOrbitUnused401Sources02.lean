import QiushiGlobalOrbitUnused401Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit41FP
import QiushiStep128Mono246From75
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane401UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [261, 163, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(261, 97), (163, 431), (96, 430), (20, 306), (10, 20)]
    (codeMat 93) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane401UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [261, 164, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(261, 437), (164, 80), (96, 507), (20, 168), (10, 327)]
    (codeMat 415) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane401UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [261, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(261, 274), (166, 399), (96, 137), (20, 252), (10, 507)]
    (codeMat 102) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane401UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [261, 167, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(261, 371), (167, 359), (96, 252), (20, 21), (10, 495)]
    (codeMat 415) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane401UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [261, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(261, 43), (64, 3), (32, 9), (20, 118), (8, 1), (2, 384)]
    (codeMat 498) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane401UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 408), (64, 45), (32, 32), (19, 166), (10, 404), (7, 438)]
    (codeMat 158) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_262_row11_qr

theorem plane401UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [261, 135, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(261, 30), (135, 238), (67, 435), (35, 422), (20, 160), (10, 434)]
    (codeMat 215) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane401UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (129, 162), (96, 68), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane401UnusedGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane401UnusedGenSource0029 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 232), (129, 246), (66, 374), (34, 11), (18, 9), (10, 137), (6, 3)]
    (codeMat 467) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
