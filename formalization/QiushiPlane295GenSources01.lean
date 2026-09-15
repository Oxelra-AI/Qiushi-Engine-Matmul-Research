import QiushiPlane295GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane295GenSource0010 :
    QuotientRankAtLeast (spanCodes [272, 66, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 104), (66, 148), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 401) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane295GenSource0011 :
    QuotientRankAtLeast (spanCodes [272, 80, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (80, 224), (32, 8), (10, 28), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane295GenSource0012 :
    QuotientRankAtLeast (spanCodes [272, 82, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 104), (82, 252), (32, 8), (10, 28), (4, 1), (1, 3)]
    (codeMat 401) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane295GenSource0013 :
    QuotientRankAtLeast (spanCodes [272, 150, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(272, 11), (150, 43), (32, 1), (10, 126), (1, 432)]
    (codeMat 354) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane295GenSource0014 :
    QuotientRankAtLeast (spanCodes [272, 130, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 283), (130, 260), (70, 462), (32, 192), (10, 160), (1, 432)]
    (codeMat 159) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane295GenSource0015 :
    QuotientRankAtLeast (spanCodes [272, 208, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(272, 316), (208, 138), (32, 32), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane295GenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 32, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 2), (32, 1), (16, 8), (10, 96), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane295GenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 130, 66, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(272, 274), (130, 45), (66, 13), (32, 438), (10, 15), (1, 1)]
    (codeMat 305) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane295GenSource0018 :
    QuotientRankAtLeast (spanCodes [272, 150, 82, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(272, 274), (150, 148), (82, 31), (32, 128), (10, 224), (1, 504)]
    (codeMat 159) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane295GenSource0019 :
    QuotientRankAtLeast (spanCodes [272, 130, 82, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(272, 42), (130, 325), (82, 366), (32, 63), (10, 347), (1, 192)]
    (codeMat 116) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

end QiushiMatmul
