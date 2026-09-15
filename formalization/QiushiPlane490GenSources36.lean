import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0360 :
    QuotientRankAtLeast (spanCodes [275, 144, 65, 39, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(275, 397), (144, 128), (65, 390), (39, 295), (10, 294)]
    (codeMat 443) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane490GenSource0361 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 39, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 78), (134, 79), (66, 507), (39, 160), (21, 336), (10, 480)]
    (codeMat 212) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0362 :
    QuotientRankAtLeast (spanCodes [262, 130, 67, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 96), (130, 8), (67, 97), (34, 224), (21, 28), (10, 227)]
    (codeMat 125) (codeMat 337) (codeMat 337) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0363 :
    QuotientRankAtLeast (spanCodes [256, 165, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (165, 85), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0364 :
    QuotientRankAtLeast (spanCodes [259, 130, 70, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(259, 68), (130, 2), (70, 71), (34, 160), (16, 16), (10, 184)]
    (codeMat 85) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane490GenSource0365 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0366 :
    QuotientRankAtLeast (spanCodes [259, 133, 65, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 148), (133, 20), (65, 130), (34, 104), (16, 8), (10, 97)]
    (codeMat 106) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0367 :
    QuotientRankAtLeast (spanCodes [259, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (130, 3), (68, 255), (32, 128), (16, 2), (10, 150)]
    (codeMat 87) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0368 :
    QuotientRankAtLeast (spanCodes [258, 135, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 232), (135, 96), (71, 224), (39, 150), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0369 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (132, 96), (68, 224), (39, 148), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
