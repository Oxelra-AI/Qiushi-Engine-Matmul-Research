import QiushiPlane254GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit108From29
import QiushiOrbit10FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane254GenSource0010 :
    QuotientRankAtLeast (spanCodes [164, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(164, 246), (84, 94), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane254GenSource0011 :
    QuotientRankAtLeast (spanCodes [176, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(176, 160), (84, 86), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane254GenSource0012 :
    QuotientRankAtLeast (spanCodes [180, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(180, 252), (84, 92), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane254GenSource0013 :
    QuotientRankAtLeast (spanCodes [256, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 256), (80, 80), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0014 :
    QuotientRankAtLeast (spanCodes [272, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(272, 336), (80, 80), (8, 8), (4, 5), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0015 :
    QuotientRankAtLeast (spanCodes [292, 64, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(292, 256), (64, 7), (20, 80), (8, 2), (2, 8), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0016 :
    QuotientRankAtLeast (spanCodes [288, 64, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(288, 256), (64, 6), (20, 80), (8, 2), (2, 8), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0017 :
    QuotientRankAtLeast (spanCodes [292, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(292, 511), (164, 255), (68, 184), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane254GenSource0018 :
    QuotientRankAtLeast (spanCodes [388, 64, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(388, 264), (64, 5), (20, 88), (8, 2), (2, 8), (1, 1)]
    (codeMat 337) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0019 :
    QuotientRankAtLeast (spanCodes [384, 64, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(384, 256), (64, 4), (20, 88), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

end QiushiMatmul
