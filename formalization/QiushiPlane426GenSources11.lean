import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0110 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(262, 11), (130, 1), (70, 52), (22, 80), (10, 264), (1, 32)]
    (codeMat 141) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane426GenSource0111 :
    QuotientRankAtLeast (spanCodes [262, 166, 98, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(262, 127), (166, 398), (98, 106), (22, 496), (10, 272), (1, 128)]
    (codeMat 95) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane426GenSource0112 :
    QuotientRankAtLeast (spanCodes [260, 162, 100, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(260, 1), (162, 11), (100, 357), (20, 90), (10, 180), (1, 288)]
    (codeMat 445) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane426GenSource0113 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (128, 8), (64, 1), (20, 224), (10, 28), (1, 3)]
    (codeMat 172) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0114 :
    QuotientRankAtLeast (spanCodes [262, 132, 70, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(262, 43), (132, 53), (70, 20), (22, 344), (10, 264), (1, 32)]
    (codeMat 205) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane426GenSource0115 :
    QuotientRankAtLeast (spanCodes [256, 160, 100, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 16), (160, 10), (100, 170), (16, 1), (10, 69), (1, 320)]
    (codeMat 98) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0116 :
    QuotientRankAtLeast (spanCodes [272, 160, 114, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 148), (160, 150), (114, 125), (10, 105), (6, 1), (1, 8)]
    (codeMat 177) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0117 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 136), (128, 8), (64, 1), (22, 224), (10, 28), (1, 3)]
    (codeMat 172) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0118 :
    QuotientRankAtLeast (spanCodes [272, 150, 82, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 367), (150, 223), (82, 203), (36, 1), (10, 97), (1, 260)]
    (codeMat 99) (codeMat 215) (codeMat 342) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane426GenSource0119 :
    QuotientRankAtLeast (spanCodes [272, 148, 70, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(272, 91), (148, 11), (70, 264), (50, 81), (10, 316), (1, 32)]
    (codeMat 271) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
