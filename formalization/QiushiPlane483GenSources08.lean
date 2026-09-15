import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiStep128Mono189From80T
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0080 :
    QuotientRankAtLeast (spanCodes [278, 160, 80, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(278, 373), (160, 341), (80, 133), (14, 10), (1, 1)]
    (codeMat 465) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane483GenSource0081 :
    QuotientRankAtLeast (spanCodes [260, 160, 76, 28, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(260, 32), (160, 341), (76, 10), (28, 496), (1, 1)]
    (codeMat 369) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane483GenSource0082 :
    QuotientRankAtLeast (spanCodes [262, 160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 506), (160, 341), (74, 10), (20, 133), (1, 1)]
    (codeMat 241) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane483GenSource0083 :
    QuotientRankAtLeast (spanCodes [280, 148, 74, 52, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(280, 276), (148, 30), (74, 11), (52, 363), (1, 1)]
    (codeMat 369) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane483GenSource0084 :
    QuotientRankAtLeast (spanCodes [128, 78, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(128, 128), (78, 284), (32, 1), (20, 10), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane483GenSource0085 :
    QuotientRankAtLeast (spanCodes [268, 140, 44, 22, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(268, 278), (140, 279), (44, 406), (22, 138), (1, 438)]
    (codeMat 412) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane483GenSource0086 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(258, 10), (128, 1), (32, 32), (20, 20), (1, 128)]
    (codeMat 140) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane483GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 22, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 367), (160, 453), (66, 366), (22, 464), (14, 272), (1, 432)]
    (codeMat 156) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane483GenSource0088 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 20, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 447), (160, 462), (66, 420), (20, 112), (14, 352), (1, 256)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane483GenSource0089 :
    QuotientRankAtLeast (spanCodes [256, 140, 88, 44, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (140, 117), (88, 43), (44, 127), (1, 384)]
    (codeMat 116) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
