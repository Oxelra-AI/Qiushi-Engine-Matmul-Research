import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0340 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 37, 20, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 104), (134, 96), (64, 9), (37, 252), (20, 224), (14, 31)]
    (codeMat 124) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0341 :
    QuotientRankAtLeast (spanCodes [260, 138, 64, 40, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 3), (138, 20), (64, 130), (40, 8), (20, 224), (1, 128)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0342 :
    QuotientRankAtLeast (spanCodes [268, 128, 66, 34, 22, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(268, 164), (128, 1), (66, 10), (34, 446), (22, 113), (1, 16)]
    (codeMat 460) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0343 :
    QuotientRankAtLeast (spanCodes [259, 132, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 176), (132, 480), (64, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 299) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0344 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 37, 22, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 222), (134, 437), (66, 223), (37, 97), (22, 430), (11, 479)]
    (codeMat 468) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0345 :
    QuotientRankAtLeast (spanCodes [263, 128, 65, 35, 21, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 497), (128, 260), (65, 27), (35, 496), (21, 176), (11, 480)]
    (codeMat 215) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0346 :
    QuotientRankAtLeast (spanCodes [258, 129, 71, 34, 19, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 507), (129, 436), (71, 506), (34, 480), (19, 176), (9, 16)]
    (codeMat 157) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0347 :
    QuotientRankAtLeast (spanCodes [262, 131, 70, 32, 18, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 506), (131, 437), (70, 507), (32, 16), (18, 320), (14, 480)]
    (codeMat 212) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0348 :
    QuotientRankAtLeast (spanCodes [261, 131, 69, 32, 17, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 245), (131, 497), (69, 238), (32, 320), (17, 496), (14, 160)]
    (codeMat 159) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0349 :
    QuotientRankAtLeast (spanCodes [258, 133, 70, 38, 18, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 353), (133, 180), (70, 175), (38, 352), (18, 256), (12, 112)]
    (codeMat 215) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
