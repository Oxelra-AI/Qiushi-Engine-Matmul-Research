import QiushiGlobalOrbitUnused402Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit75Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane402UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [262, 128, 96, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(262, 493), (128, 128), (96, 139), (20, 255), (10, 280), (1, 504)]
    (codeMat 230) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane402UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [387, 66, 34, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(387, 287), (66, 441), (34, 12), (16, 1), (10, 15), (4, 45)]
    (codeMat 474) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_262_row11_qr

theorem plane402UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [262, 129, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 322), (129, 343), (69, 191), (37, 274), (20, 262), (10, 180)]
    (codeMat 207) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane402UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [257, 134, 71, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 160, 68, 16, 10, 1] [(257, 327), (134, 259), (71, 69), (39, 440), (20, 280), (10, 424)]
    (codeMat 92) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc204s0Dispatch

theorem plane402UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (134, 353), (66, 404), (34, 105), (20, 97), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane402UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 118), (128, 128), (64, 256), (32, 1), (16, 2), (10, 22), (4, 9)]
    (codeMat 282) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane402UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane402UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 131), (131, 139), (64, 9), (32, 256), (19, 483), (10, 252), (7, 3)]
    (codeMat 172) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane402UnusedGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 130), (67, 381), (35, 363), (19, 235), (10, 373), (7, 360)]
    (codeMat 423) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane402UnusedGenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 10, 6, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 325), (128, 260), (66, 227), (34, 328), (18, 256), (10, 248), (6, 8), (1, 24)]
    (codeMat 207) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
