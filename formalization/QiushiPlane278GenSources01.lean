import QiushiPlane278GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane278GenSource0010 :
    QuotientRankAtLeast (spanCodes [260, 140, 72, 40, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 511), (140, 185), (72, 3), (40, 256), (28, 184), (2, 8), (1, 24)]
    (codeMat 142) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane278GenSource0011 :
    QuotientRankAtLeast (spanCodes [264, 132, 64, 32, 24, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 96), (132, 28), (64, 8), (32, 256), (24, 128), (2, 3), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane278GenSource0012 :
    QuotientRankAtLeast (spanCodes [292, 128, 96, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(292, 360), (128, 130), (96, 235), (20, 21), (12, 29), (2, 2), (1, 3)]
    (codeMat 337) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane278GenSource0013 :
    QuotientRankAtLeast (spanCodes [292, 132, 96, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(292, 384), (132, 148), (96, 235), (20, 22), (12, 30), (2, 2), (1, 3)]
    (codeMat 465) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane278GenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 140, 72, 40, 24, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (140, 157), (72, 8), (40, 256), (24, 128), (2, 3), (1, 1)]
    (codeMat 177) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane278GenSource0015 :
    QuotientRankAtLeast (spanCodes [288, 168, 96, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(288, 40), (168, 272), (96, 408), (16, 128), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane278GenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 80, 48, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 8), (80, 336), (48, 256), (4, 1), (2, 5), (1, 2)]
    (codeMat 161) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane278GenSource0017 :
    QuotientRankAtLeast (spanCodes [304, 128, 96, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(304, 264), (128, 8), (96, 344), (4, 5), (2, 1), (1, 6)]
    (codeMat 417) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane278GenSource0018 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(272, 80), (64, 256), (32, 8), (4, 1), (2, 2), (1, 4)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane278GenSource0019 :
    QuotientRankAtLeast (spanCodes [304, 144, 96, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(304, 88), (144, 8), (96, 336), (4, 2), (2, 1), (1, 7)]
    (codeMat 305) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

end QiushiMatmul
