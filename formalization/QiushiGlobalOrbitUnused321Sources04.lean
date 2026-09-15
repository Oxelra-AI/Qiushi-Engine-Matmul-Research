import QiushiGlobalOrbitUnused321Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane321UnusedGenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 150), (132, 148), (64, 256), (36, 360), (20, 363), (10, 374), (1, 384)]
    (codeMat 303) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (132, 224), (66, 31), (36, 360), (20, 232), (10, 30), (1, 3)]
    (codeMat 382) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0042 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (128, 8), (64, 1), (32, 384), (22, 232), (10, 30), (1, 3)]
    (codeMat 492) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 20), (64, 128), (36, 3), (22, 28), (10, 480), (1, 256)]
    (codeMat 103) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (134, 373), (66, 406), (38, 413), (22, 245), (10, 278), (1, 130)]
    (codeMat 423) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0045 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 256), (128, 130), (68, 69), (32, 32), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane321UnusedGenSource0046 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 288), (132, 148), (68, 76), (36, 32), (20, 22), (8, 9), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane321UnusedGenSource0047 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 150), (130, 288), (64, 219), (34, 22), (18, 32), (10, 31), (4, 2), (1, 3)]
    (codeMat 409) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane321UnusedGenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 384), (128, 256), (66, 196), (32, 54), (18, 32), (10, 31), (6, 2), (1, 3)]
    (codeMat 281) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
