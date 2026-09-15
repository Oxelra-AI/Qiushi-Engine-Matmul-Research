import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0010 :
    QuotientRankAtLeast (spanCodes [260, 160, 70, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 320), (160, 245), (70, 160), (16, 27), (10, 10), (1, 16)]
    (codeMat 331) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane315GenSource0011 :
    QuotientRankAtLeast (spanCodes [260, 134, 70, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(260, 1), (134, 11), (70, 52), (38, 81), (10, 284), (1, 32)]
    (codeMat 461) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane315GenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (160, 148), (96, 20), (10, 104), (4, 1), (1, 8)]
    (codeMat 161) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane315GenSource0013 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 3), (134, 28), (64, 9), (38, 224), (10, 104), (1, 8)]
    (codeMat 205) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane315GenSource0014 :
    QuotientRankAtLeast (spanCodes [260, 160, 112, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(260, 32), (160, 484), (112, 411), (10, 462), (1, 432)]
    (codeMat 303) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane315GenSource0015 :
    QuotientRankAtLeast (spanCodes [260, 148, 70, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 27), (148, 197), (70, 164), (52, 368), (10, 96), (1, 256)]
    (codeMat 94) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane315GenSource0016 :
    QuotientRankAtLeast (spanCodes [260, 146, 70, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 1), (146, 260), (70, 222), (50, 96), (10, 160), (1, 432)]
    (codeMat 157) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane315GenSource0017 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 1), (160, 462), (96, 202), (20, 127), (10, 475), (1, 192)]
    (codeMat 125) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane315GenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 134, 80, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 192), (134, 475), (80, 170), (38, 356), (10, 97), (1, 260)]
    (codeMat 115) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane315GenSource0019 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(260, 1), (160, 398), (96, 138), (22, 496), (10, 400), (1, 128)]
    (codeMat 85) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

end QiushiMatmul
