import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0100 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (130, 16), (67, 176), (39, 437), (20, 506), (10, 436)]
    (codeMat 299) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane457GenSource0101 :
    QuotientRankAtLeast (spanCodes [259, 129, 67, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 362), (129, 222), (67, 363), (36, 16), (20, 272), (10, 368)]
    (codeMat 156) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0102 :
    QuotientRankAtLeast (spanCodes [262, 132, 67, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 222), (132, 437), (67, 223), (33, 97), (20, 430), (10, 479)]
    (codeMat 477) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0103 :
    QuotientRankAtLeast (spanCodes [289, 224, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(289, 427), (224, 11), (18, 511), (10, 510), (6, 384)]
    (codeMat 354) (codeMat 254) (codeMat 443) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane457GenSource0104 :
    QuotientRankAtLeast (spanCodes [288, 160, 65, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 256), (160, 283), (65, 1), (19, 463), (10, 113), (7, 16)]
    (codeMat 397) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0105 :
    QuotientRankAtLeast (spanCodes [291, 162, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(291, 357), (162, 126), (64, 192), (16, 432), (10, 160), (4, 260)]
    (codeMat 95) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane457GenSource0106 :
    QuotientRankAtLeast (spanCodes [289, 161, 65, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 352), (161, 379), (65, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 461) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0107 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(257, 33), (129, 34), (65, 32), (16, 438), (10, 274), (4, 45)]
    (codeMat 236) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane457GenSource0108 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 45), (128, 2), (68, 44), (20, 168), (10, 272), (1, 32)]
    (codeMat 140) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane457GenSource0109 :
    QuotientRankAtLeast (spanCodes [260, 135, 66, 39, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 45), (135, 287), (66, 441), (39, 408), (20, 168), (10, 440)]
    (codeMat 158) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
