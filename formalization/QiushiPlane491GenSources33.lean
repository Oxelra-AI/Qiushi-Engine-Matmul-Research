import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0330 :
    QuotientRankAtLeast (spanCodes [262, 128, 72, 35, 28]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(262, 272), (128, 256), (72, 27), (35, 78), (28, 79)]
    (codeMat 299) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane491GenSource0331 :
    QuotientRankAtLeast (spanCodes [261, 130, 65, 33, 21, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 22), (130, 128), (65, 2), (33, 31), (21, 224), (8, 3)]
    (codeMat 111) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0332 :
    QuotientRankAtLeast (spanCodes [260, 131, 65, 32, 21, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(260, 3), (131, 68), (65, 1), (32, 24), (21, 160), (8, 8)]
    (codeMat 85) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane491GenSource0333 :
    QuotientRankAtLeast (spanCodes [262, 128, 66, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 336), (128, 16), (66, 176), (35, 79), (22, 506), (10, 436)]
    (codeMat 355) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0334 :
    QuotientRankAtLeast (spanCodes [257, 134, 68, 37, 16, 13]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 28), (134, 224), (68, 31), (37, 20), (16, 128), (13, 22)]
    (codeMat 87) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0335 :
    QuotientRankAtLeast (spanCodes [260, 134, 65, 37, 21, 13]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 8), (134, 104), (65, 9), (37, 20), (21, 148), (13, 22)]
    (codeMat 85) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0336 :
    QuotientRankAtLeast (spanCodes [256, 135, 69, 36, 17, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 130), (135, 126), (69, 139), (36, 128), (17, 232), (12, 136)]
    (codeMat 215) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0337 :
    QuotientRankAtLeast (spanCodes [293, 163, 68, 16, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(293, 33), (163, 161), (68, 42), (16, 438), (12, 43)]
    (codeMat 494) (codeMat 183) (codeMat 419) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0338 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 33, 18, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 104), (130, 8), (70, 232), (33, 148), (18, 1), (12, 150)]
    (codeMat 299) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0339 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 33, 22, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 480), (130, 320), (66, 336), (33, 507), (22, 437), (15, 79)]
    (codeMat 354) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
