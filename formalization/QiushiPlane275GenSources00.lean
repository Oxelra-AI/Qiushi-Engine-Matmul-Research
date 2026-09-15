import QiushiPlane275GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit108From29
import QiushiMonoOrbit110From29
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit123From35
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit134From35T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane275GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(160, 160), (84, 84), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane275GenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 84, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(160, 240), (84, 94), (12, 14), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane275GenSource0002 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(160, 96), (68, 132), (16, 8), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane275GenSource0003 :
    QuotientRankAtLeast (spanCodes [160, 64, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 272), (64, 2), (20, 96), (2, 8), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane275GenSource0004 :
    QuotientRankAtLeast (spanCodes [160, 76, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(160, 237), (76, 134), (24, 9), (2, 3), (1, 2)]
    (codeMat 409) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane275GenSource0005 :
    QuotientRankAtLeast (spanCodes [160, 72, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 274), (72, 2), (28, 105), (2, 9), (1, 1)]
    (codeMat 177) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane275GenSource0006 :
    QuotientRankAtLeast (spanCodes [132, 84, 36, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(132, 12), (84, 93), (36, 256), (2, 1), (1, 3)]
    (codeMat 225) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane275GenSource0007 :
    QuotientRankAtLeast (spanCodes [136, 84, 40, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(136, 80), (84, 95), (40, 256), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane275GenSource0008 :
    QuotientRankAtLeast (spanCodes [152, 84, 56, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(152, 80), (84, 206), (56, 32), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane275GenSource0009 :
    QuotientRankAtLeast (spanCodes [156, 84, 60, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(156, 204), (84, 158), (60, 33), (2, 3), (1, 2)]
    (codeMat 281) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

end QiushiMatmul
