import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0080 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (128, 384), (68, 488), (33, 381), (21, 406), (9, 511), (3, 8)]
    (codeMat 270) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0081 :
    QuotientRankAtLeast (spanCodes [289, 160, 65, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 127), (160, 287), (65, 8), (17, 131), (9, 1), (5, 384), (3, 128)]
    (codeMat 107) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0082 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (132, 326), (68, 324), (32, 40), (20, 368), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane465GenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 452), (130, 455), (64, 2), (32, 32), (18, 504), (10, 464), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane465GenSource0084 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 199), (64, 3), (33, 208), (17, 248), (9, 216), (4, 128), (3, 256)]
    (codeMat 84) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane465GenSource0085 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane465GenSource0086 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 16, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 327), (129, 324), (65, 325), (33, 376), (16, 32), (8, 40), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane465GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 453), (130, 455), (66, 454), (32, 40), (18, 504), (10, 496), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
