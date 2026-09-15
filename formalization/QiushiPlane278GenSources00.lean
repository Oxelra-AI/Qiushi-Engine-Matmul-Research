import QiushiPlane278GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit130From35T
import QiushiOrbit10FP
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit146Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane278GenSource0000 :
    QuotientRankAtLeast (spanCodes [304, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(304, 376), (96, 104), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane278GenSource0001 :
    QuotientRankAtLeast (spanCodes [276, 68, 36, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(276, 162), (68, 13), (36, 256), (2, 2), (1, 1)]
    (codeMat 233) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane278GenSource0002 :
    QuotientRankAtLeast (spanCodes [284, 76, 44, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(284, 430), (76, 12), (44, 257), (2, 2), (1, 1)]
    (codeMat 249) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane278GenSource0003 :
    QuotientRankAtLeast (spanCodes [304, 180, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(304, 297), (180, 264), (96, 350), (2, 1), (1, 3)]
    (codeMat 233) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane278GenSource0004 :
    QuotientRankAtLeast (spanCodes [304, 172, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(304, 119), (172, 267), (96, 350), (2, 1), (1, 3)]
    (codeMat 249) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane278GenSource0005 :
    QuotientRankAtLeast (spanCodes [304, 140, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(304, 495), (140, 84), (96, 333), (2, 2), (1, 1)]
    (codeMat 225) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane278GenSource0006 :
    QuotientRankAtLeast (spanCodes [304, 156, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(304, 162), (156, 85), (96, 333), (2, 2), (1, 1)]
    (codeMat 241) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane278GenSource0007 :
    QuotientRankAtLeast (spanCodes [292, 164, 96, 20, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(292, 438), (164, 406), (96, 408), (20, 134), (2, 2), (1, 3)]
    (codeMat 161) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane278GenSource0008 :
    QuotientRankAtLeast (spanCodes [292, 168, 96, 20, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(292, 45), (168, 272), (96, 408), (20, 133), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane278GenSource0009 :
    QuotientRankAtLeast (spanCodes [268, 128, 64, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 228), (128, 1), (64, 3), (32, 256), (28, 160), (2, 8), (1, 24)]
    (codeMat 140) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
