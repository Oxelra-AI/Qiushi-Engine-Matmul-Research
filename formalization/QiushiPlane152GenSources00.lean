import QiushiPlane152GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiOrbit29FP
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane152GenSource0000 :
    QuotientRankAtLeast (spanCodes [164, 96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(164, 228), (96, 68), (16, 3), (8, 1), (2, 24), (1, 8)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane152GenSource0001 :
    QuotientRankAtLeast (spanCodes [256, 164, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (164, 196), (96, 164), (16, 27), (10, 10), (1, 16)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane152GenSource0002 :
    QuotientRankAtLeast (spanCodes [262, 164, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 430), (164, 197), (96, 180), (16, 27), (10, 10), (1, 16)]
    (codeMat 459) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane152GenSource0003 :
    QuotientRankAtLeast (spanCodes [290, 164, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(290, 479), (164, 223), (96, 175), (16, 27), (10, 10), (1, 16)]
    (codeMat 331) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane152GenSource0004 :
    QuotientRankAtLeast (spanCodes [294, 164, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(294, 368), (164, 222), (96, 191), (16, 27), (10, 10), (1, 16)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane152GenSource0005 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 149), (96, 148), (16, 360), (10, 96), (4, 128), (1, 256)]
    (codeMat 92) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane152GenSource0006 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 20), (64, 1), (32, 128), (16, 256), (10, 96), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane152GenSource0007 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (130, 1), (70, 509), (38, 136), (16, 8), (10, 96), (1, 360)]
    (codeMat 213) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane152GenSource0008 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 227), (134, 284), (66, 105), (34, 224), (16, 256), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane152GenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (128, 9), (68, 413), (36, 384), (16, 8), (10, 96), (1, 360)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
