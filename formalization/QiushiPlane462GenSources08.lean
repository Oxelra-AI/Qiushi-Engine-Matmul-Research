import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (128, 1), (68, 104), (34, 20), (16, 2), (10, 148)]
    (codeMat 84) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0081 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 136), (130, 128), (68, 232), (32, 3), (16, 2), (10, 150)]
    (codeMat 354) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0082 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 52, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(261, 43), (133, 11), (68, 30), (52, 310), (9, 365), (3, 63)]
    (codeMat 165) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0083 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 55, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(260, 32), (133, 10), (68, 33), (55, 469), (10, 350)]
    (codeMat 428) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane462GenSource0084 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 38, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 320), (133, 160), (68, 336), (38, 437), (17, 78), (10, 79)]
    (codeMat 355) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane462GenSource0085 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 104), (128, 128), (68, 96), (34, 148), (16, 2), (10, 149)]
    (codeMat 298) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0086 :
    QuotientRankAtLeast (spanCodes [259, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (130, 3), (68, 255), (32, 128), (16, 2), (10, 150)]
    (codeMat 87) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0087 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(257, 79), (128, 365), (68, 78), (37, 112), (23, 264), (10, 344)]
    (codeMat 213) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0088 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (135, 105), (68, 104), (36, 128), (17, 150), (10, 148)]
    (codeMat 93) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0089 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (132, 96), (68, 224), (39, 148), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
