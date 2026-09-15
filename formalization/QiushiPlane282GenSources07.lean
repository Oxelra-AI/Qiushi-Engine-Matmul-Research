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

theorem plane282GenSource0070 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 406), (128, 130), (68, 227), (34, 150), (16, 2), (10, 149), (1, 511)]
    (codeMat 426) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0071 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 31), (132, 28), (64, 9), (34, 480), (16, 256), (10, 96), (1, 8)]
    (codeMat 141) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 406), (132, 276), (66, 105), (32, 384), (16, 256), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 128, 96, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 127), (128, 9), (96, 28), (16, 8), (10, 96), (6, 384), (1, 256)]
    (codeMat 86) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane282GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 194, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (194, 240), (32, 9), (16, 54), (10, 29), (4, 8), (1, 40)]
    (codeMat 267) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0076 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (132, 160), (96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane282GenSource0077 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane282GenSource0078 :
    QuotientRankAtLeast (spanCodes [256, 68, 36, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (68, 96), (36, 4), (16, 18), (8, 9), (2, 16), (1, 8)]
    (codeMat 267) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane282GenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 66, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(258, 112), (66, 118), (34, 96), (16, 256), (10, 100), (4, 8), (1, 9)]
    (codeMat 177) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
