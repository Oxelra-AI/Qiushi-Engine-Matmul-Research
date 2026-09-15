import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0380 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(261, 228), (129, 137), (64, 219), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0381 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 501), (145, 503), (81, 502), (49, 176), (9, 432), (5, 24), (3, 8)]
    (codeMat 140) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0382 :
    QuotientRankAtLeast (spanCodes [257, 144, 64, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 138), (144, 54), (64, 219), (32, 128), (9, 216), (5, 8), (3, 40)]
    (codeMat 143) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0383 :
    QuotientRankAtLeast (spanCodes [385, 64, 32, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(385, 80), (64, 128), (32, 54), (16, 63), (9, 2), (5, 32), (3, 40)]
    (codeMat 267) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0384 :
    QuotientRankAtLeast (spanCodes [262, 130, 64, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(262, 196), (130, 3), (64, 130), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 85) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0385 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 71), (134, 70), (70, 68), (38, 440), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0386 :
    QuotientRankAtLeast (spanCodes [272, 130, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 70), (130, 511), (66, 186), (34, 440), (10, 184), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0387 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 238), (128, 325), (66, 170), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0388 :
    QuotientRankAtLeast (spanCodes [386, 64, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 199), (64, 128), (32, 32), (18, 63), (10, 23), (6, 3), (1, 2)]
    (codeMat 273) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0389 :
    QuotientRankAtLeast (spanCodes [256, 144, 66, 34, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 216), (144, 32), (66, 76), (34, 196), (10, 68), (4, 3), (1, 1)]
    (codeMat 177) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
