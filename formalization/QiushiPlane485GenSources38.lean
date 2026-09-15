import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0380 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 80), (128, 216), (65, 32), (32, 2), (16, 3), (10, 196), (4, 128)]
    (codeMat 106) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0381 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (133, 327), (65, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0382 :
    QuotientRankAtLeast (spanCodes [261, 133, 69, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(261, 198), (133, 199), (69, 197), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 92) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0383 :
    QuotientRankAtLeast (spanCodes [260, 132, 69, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 9), (132, 210), (69, 100), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0384 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (133, 68), (64, 3), (32, 16), (20, 160), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0385 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 22), (129, 81), (64, 130), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 142) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0386 :
    QuotientRankAtLeast (spanCodes [256, 193, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (193, 248), (33, 42), (17, 28), (8, 63), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0387 :
    QuotientRankAtLeast (spanCodes [257, 192, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 240), (192, 128), (33, 43), (17, 20), (8, 54), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0388 :
    QuotientRankAtLeast (spanCodes [321, 129, 33, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 248), (129, 120), (33, 28), (16, 9), (8, 63), (4, 32), (2, 8)]
    (codeMat 267) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0389 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 30), (134, 29), (64, 1), (38, 414), (20, 373), (10, 105), (1, 8)]
    (codeMat 396) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
