import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0190 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (130, 8), (64, 2), (20, 224), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0191 :
    QuotientRankAtLeast (spanCodes [289, 162, 67, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(289, 261), (162, 186), (67, 420), (16, 16), (10, 160), (4, 320)]
    (codeMat 86) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0192 :
    QuotientRankAtLeast (spanCodes [258, 163, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (163, 157), (96, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0193 :
    QuotientRankAtLeast (spanCodes [289, 163, 66, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(289, 321), (163, 254), (66, 420), (17, 176), (10, 160), (5, 320)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0194 :
    QuotientRankAtLeast (spanCodes [289, 130, 99, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(289, 347), (130, 260), (99, 94), (17, 160), (10, 176), (5, 320)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0195 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (128, 8), (64, 1), (20, 224), (10, 28), (1, 3)]
    (codeMat 172) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0196 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 20), (128, 9), (65, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 141) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0197 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 22), (129, 11), (65, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 205) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0198 :
    QuotientRankAtLeast (spanCodes [258, 135, 66, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(258, 43), (135, 33), (66, 42), (20, 350), (10, 469)]
    (codeMat 492) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane485GenSource0199 :
    QuotientRankAtLeast (spanCodes [291, 227, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(291, 33), (227, 35), (19, 462), (10, 441), (7, 1)]
    (codeMat 481) (codeMat 234) (codeMat 461) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
