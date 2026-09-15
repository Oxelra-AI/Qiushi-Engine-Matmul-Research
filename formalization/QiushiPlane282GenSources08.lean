import QiushiPlane282GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit118From31
import QiushiMonoOrbit121From55
import QiushiMonoOrbit151From65
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit31FP
import QiushiStep98Orbit153Mono
import QiushiStep99Mono3032
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane282GenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 96, 16, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (96, 96), (16, 16), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0081 :
    QuotientRankAtLeast (spanCodes [256, 132, 32, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (132, 96), (32, 4), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0082 :
    QuotientRankAtLeast (spanCodes [256, 164, 100, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (164, 96), (100, 100), (16, 24), (8, 27), (2, 16), (1, 18)]
    (codeMat 267) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(258, 22), (130, 4), (64, 9), (16, 256), (10, 96), (6, 16), (1, 8)]
    (codeMat 141) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0084 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 16, 10, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(258, 118), (128, 9), (66, 100), (34, 112), (16, 8), (10, 96), (1, 256)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0085 :
    QuotientRankAtLeast (spanCodes [256, 196, 36, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (196, 96), (36, 4), (16, 18), (8, 27), (2, 16), (1, 24)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0086 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 324), (130, 325), (66, 326), (32, 32), (16, 40), (10, 368), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane282GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 326), (130, 325), (64, 2), (34, 368), (16, 40), (10, 336), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane282GenSource0088 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (128, 1), (66, 70), (32, 40), (16, 8), (10, 112), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane282GenSource0089 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 71), (128, 1), (64, 2), (34, 120), (16, 8), (10, 80), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
