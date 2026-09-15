import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0140 :
    QuotientRankAtLeast (spanCodes [258, 128, 76, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 15), (128, 1), (76, 164), (36, 45), (16, 3), (1, 438)]
    (codeMat 500) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0141 :
    QuotientRankAtLeast (spanCodes [256, 138, 68, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (138, 274), (68, 12), (36, 3), (16, 438), (1, 45)]
    (codeMat 380) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0142 :
    QuotientRankAtLeast (spanCodes [268, 128, 66, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(268, 319), (128, 1), (66, 12), (36, 438), (16, 3), (1, 45)]
    (codeMat 372) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0143 :
    QuotientRankAtLeast (spanCodes [262, 136, 64, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(262, 137), (136, 12), (64, 1), (36, 438), (16, 45), (1, 3)]
    (codeMat 428) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0144 :
    QuotientRankAtLeast (spanCodes [264, 134, 64, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(264, 15), (134, 137), (64, 1), (36, 45), (16, 438), (1, 3)]
    (codeMat 492) (codeMat 183) (codeMat 419) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0145 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 301), (132, 100), (66, 402), (36, 360), (16, 32), (14, 80), (1, 128)]
    (codeMat 87) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane427GenSource0146 :
    QuotientRankAtLeast (spanCodes [256, 132, 36, 16, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (132, 80), (36, 2), (16, 9), (12, 52), (2, 8), (1, 32)]
    (codeMat 267) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0147 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 88), (130, 216), (32, 1), (16, 3), (10, 28), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0148 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (128, 2), (66, 20), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 140) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0149 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 11), (130, 2), (66, 52), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 141) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
