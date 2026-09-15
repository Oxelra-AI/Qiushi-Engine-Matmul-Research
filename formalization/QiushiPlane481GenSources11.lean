import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiWcOrbit119Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0110 :
    QuotientRankAtLeast (spanCodes [362, 130, 16, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(362, 13), (130, 288), (16, 256), (4, 2), (1, 3)]
    (codeMat 185) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane481GenSource0111 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 390), (128, 1), (70, 450), (38, 112), (20, 456), (10, 208), (1, 128)]
    (codeMat 92) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane481GenSource0112 :
    QuotientRankAtLeast (spanCodes [128, 66, 32, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 128), (66, 80), (32, 54), (18, 2), (8, 9), (6, 32), (1, 8)]
    (codeMat 267) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane481GenSource0113 :
    QuotientRankAtLeast (spanCodes [258, 160, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 383), (160, 21), (96, 28), (18, 360), (10, 352), (6, 128), (1, 256)]
    (codeMat 86) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane481GenSource0114 :
    QuotientRankAtLeast (spanCodes [264, 128, 74, 32, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 22), (128, 8), (74, 118), (32, 2), (16, 1), (4, 128), (1, 384)]
    (codeMat 98) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane481GenSource0115 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (130, 256), (66, 264), (32, 2), (20, 148), (12, 149), (1, 360)]
    (codeMat 354) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
