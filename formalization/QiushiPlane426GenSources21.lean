import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit23FP
import QiushiOrbit41FP
import QiushiStep99Orbit56Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0210 :
    QuotientRankAtLeast (spanCodes [272, 146, 96, 10, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(272, 252), (146, 256), (96, 83), (10, 13), (4, 3), (1, 1)]
    (codeMat 473) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane426GenSource0211 :
    QuotientRankAtLeast (spanCodes [256, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 4), (32, 1), (16, 8), (10, 80), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane426GenSource0212 :
    QuotientRankAtLeast (spanCodes [272, 84, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(272, 476), (84, 84), (52, 35), (8, 9), (2, 32), (1, 8)]
    (codeMat 331) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane426GenSource0213 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 216), (68, 88), (32, 3), (20, 28), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0214 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (66, 196), (34, 20), (16, 32), (10, 28), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0215 :
    QuotientRankAtLeast (spanCodes [260, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 216), (68, 88), (36, 3), (20, 60), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0216 :
    QuotientRankAtLeast (spanCodes [256, 130, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (130, 216), (32, 2), (16, 3), (10, 28), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0217 :
    QuotientRankAtLeast (spanCodes [258, 128, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (128, 128), (34, 11), (18, 2), (10, 52), (6, 8), (1, 32)]
    (codeMat 267) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0218 :
    QuotientRankAtLeast (spanCodes [272, 144, 84, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(272, 386), (144, 2), (84, 117), (8, 32), (2, 1), (1, 8)]
    (codeMat 177) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane426GenSource0219 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 4), (128, 1), (64, 2), (16, 8), (10, 80), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
