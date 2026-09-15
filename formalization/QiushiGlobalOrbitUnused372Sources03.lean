import QiushiGlobalOrbitUnused372Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane372UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 36, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (130, 360), (70, 29), (36, 130), (20, 139), (8, 1), (1, 3)]
    (codeMat 474) (codeMat 405) (codeMat 407) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane372UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (134, 119), (66, 278), (36, 8), (20, 503), (10, 276), (1, 130)]
    (codeMat 478) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane372UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 150), (64, 128), (36, 1), (20, 361), (14, 96), (1, 256)]
    (codeMat 99) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane372UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (130, 511), (70, 480), (36, 1), (20, 361), (14, 96), (1, 256)]
    (codeMat 123) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane372UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 288), (128, 219), (68, 77), (36, 32), (20, 31), (8, 9), (2, 3), (1, 1)]
    (codeMat 409) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane372UnusedGenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 54), (132, 404), (64, 384), (36, 9), (20, 209), (12, 210), (2, 130), (1, 128)]
    (codeMat 331) (codeMat 230) (codeMat 159) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane372UnusedGenSource0036 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 288), (128, 216), (66, 80), (34, 28), (16, 3), (8, 1), (4, 32), (1, 8)]
    (codeMat 330) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
