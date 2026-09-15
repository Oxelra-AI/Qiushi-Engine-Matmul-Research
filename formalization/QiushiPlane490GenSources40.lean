import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit143Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0400 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (66, 139), (34, 134), (19, 404), (10, 166), (4, 2)]
    (codeMat 140) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0401 :
    QuotientRankAtLeast (spanCodes [256, 128, 16, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 2), (128, 1), (16, 8), (9, 360), (3, 256)]
    (codeMat 84) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane490GenSource0402 :
    QuotientRankAtLeast (spanCodes [272, 149, 48, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(272, 453), (149, 484), (48, 2), (9, 432), (3, 32)]
    (codeMat 85) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane490GenSource0403 :
    QuotientRankAtLeast (spanCodes [256, 131, 35, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (131, 441), (35, 436), (19, 404), (10, 306), (7, 438)]
    (codeMat 156) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0404 :
    QuotientRankAtLeast (spanCodes [256, 130, 32, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (130, 45), (32, 2), (19, 306), (10, 166), (6, 32)]
    (codeMat 84) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0405 :
    QuotientRankAtLeast (spanCodes [256, 129, 32, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (129, 441), (32, 2), (19, 404), (10, 166), (5, 438)]
    (codeMat 212) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0406 :
    QuotientRankAtLeast (spanCodes [256, 131, 35, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (131, 139), (35, 134), (19, 166), (10, 306), (4, 2)]
    (codeMat 140) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0407 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 18, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(257, 363), (128, 1), (65, 360), (18, 9), (10, 265)]
    (codeMat 188) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane490GenSource0408 :
    QuotientRankAtLeast (spanCodes [257, 160, 97, 18, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(257, 193), (160, 398), (97, 10), (18, 432), (10, 400), (5, 192)]
    (codeMat 85) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

theorem plane490GenSource0409 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (130, 32), (64, 2), (19, 306), (10, 166), (6, 45)]
    (codeMat 428) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
