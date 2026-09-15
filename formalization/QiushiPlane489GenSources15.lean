import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiMonoOrbit98From31T
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiPlane270GenFinal
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0150 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(258, 323), (130, 320), (66, 321), (10, 353)]
    (codeMat 372) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0151 :
    QuotientRankAtLeast (spanCodes [256, 192, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 2), (192, 1), (8, 32), (2, 320)]
    (codeMat 84) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0152 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(258, 136), (130, 8), (64, 2), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane489GenSource0153 :
    QuotientRankAtLeast (spanCodes [258, 178, 114, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 263), (178, 295), (114, 161), (10, 429), (5, 128)]
    (codeMat 117) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0154 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 43), (130, 40), (64, 2), (10, 173), (7, 9)]
    (codeMat 172) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0155 :
    QuotientRankAtLeast (spanCodes [258, 194, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 35), (194, 42), (10, 135), (6, 3), (1, 2)]
    (codeMat 169) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0156 :
    QuotientRankAtLeast (spanCodes [258, 176, 114, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 137), (176, 255), (114, 117), (10, 105), (6, 9), (1, 8)]
    (codeMat 169) (codeMat 410) (codeMat 331) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0157 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 35), (129, 47), (65, 2), (10, 168), (6, 32)]
    (codeMat 205) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0158 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 22), (128, 2), (64, 1), (10, 80), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0159 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 52), (130, 54), (64, 1), (10, 112), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
