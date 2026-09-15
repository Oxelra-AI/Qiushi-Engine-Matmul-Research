import QiushiPlane338GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit199From69
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiStep99Mono3032
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane338GenSource0010 :
    QuotientRankAtLeast (spanCodes [288, 162, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(288, 448), (162, 490), (98, 491), (16, 325), (1, 32)]
    (codeMat 396) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane338GenSource0011 :
    QuotientRankAtLeast (spanCodes [288, 164, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 132, 32, 10, 1] [(288, 1), (164, 43), (98, 337), (16, 32), (1, 511)]
    (codeMat 174) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit199_lb15_mono

theorem plane338GenSource0012 :
    QuotientRankAtLeast (spanCodes [288, 166, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 511), (166, 510), (98, 468), (16, 384), (1, 32)]
    (codeMat 141) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane338GenSource0013 :
    QuotientRankAtLeast (spanCodes [288, 172, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 511), (172, 394), (98, 468), (16, 32), (1, 384)]
    (codeMat 159) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane338GenSource0014 :
    QuotientRankAtLeast (spanCodes [288, 174, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 132, 32, 10, 1] [(288, 1), (174, 165), (98, 337), (16, 511), (1, 32)]
    (codeMat 334) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit199_lb15_mono

theorem plane338GenSource0015 :
    QuotientRankAtLeast (spanCodes [288, 98, 16, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(288, 2), (98, 98), (16, 384), (4, 1), (1, 9)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane338GenSource0016 :
    QuotientRankAtLeast (spanCodes [266, 72, 42, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(266, 163), (72, 1), (42, 160), (16, 256), (1, 8)]
    (codeMat 142) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane338GenSource0017 :
    QuotientRankAtLeast (spanCodes [288, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(288, 325), (96, 69), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane338GenSource0018 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 105), (130, 8), (68, 227), (38, 361), (16, 1), (14, 362), (1, 511)]
    (codeMat 426) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane338GenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 1), (66, 68), (32, 24), (16, 8), (14, 160), (1, 256)]
    (codeMat 84) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
