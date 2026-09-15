import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiMonoOrbit98From31T
import QiushiOrbit31FP
import QiushiPlane270GenFinal
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0140 :
    QuotientRankAtLeast (spanCodes [258, 66, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 80), (66, 82), (32, 32), (10, 100), (4, 8), (1, 9)]
    (codeMat 161) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0141 :
    QuotientRankAtLeast (spanCodes [256, 144, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 320), (144, 1), (8, 32), (2, 2)]
    (codeMat 142) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0142 :
    QuotientRankAtLeast (spanCodes [258, 128, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(258, 28), (128, 3), (34, 20), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane489GenSource0143 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(258, 136), (130, 128), (32, 3), (16, 2), (10, 148)]
    (codeMat 354) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane489GenSource0144 :
    QuotientRankAtLeast (spanCodes [258, 130, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 46), (130, 45), (36, 32), (20, 34), (10, 166)]
    (codeMat 214) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0145 :
    QuotientRankAtLeast (spanCodes [258, 130, 38, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 43), (130, 3), (38, 34), (16, 2), (10, 134)]
    (codeMat 215) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0146 :
    QuotientRankAtLeast (spanCodes [258, 144, 33, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 294), (144, 390), (33, 33), (10, 43), (5, 1)]
    (codeMat 473) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0147 :
    QuotientRankAtLeast (spanCodes [258, 146, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 35), (146, 9), (32, 2), (10, 164), (6, 32)]
    (codeMat 87) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0148 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 22), (128, 2), (32, 9), (16, 1), (10, 68), (6, 32)]
    (codeMat 98) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0149 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 52), (130, 54), (32, 8), (16, 9), (10, 100), (4, 32)]
    (codeMat 98) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
