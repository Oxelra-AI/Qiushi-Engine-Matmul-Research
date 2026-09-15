import QiushiGlobalOrbitUnused408Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiPlane315GenBindings00
import QiushiWcOrbit212Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane408UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [262, 144, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(262, 20), (144, 1), (84, 307), (51, 430), (10, 326)]
    (codeMat 302) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane408UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 151, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(262, 136), (151, 475), (84, 474), (52, 232), (10, 326)]
    (codeMat 421) (codeMat 481) (codeMat 185) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane408UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [262, 148, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 96, 10, 1] [(262, 97), (148, 406), (84, 407), (55, 280), (10, 508)]
    (codeMat 116) (codeMat 478) (codeMat 445) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit212_lb16_wc

theorem plane408UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [257, 129, 83, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 490), (129, 497), (83, 78), (34, 430), (10, 446), (7, 260)]
    (codeMat 470) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane408UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [262, 131, 65, 32, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 436), (131, 78), (65, 1), (32, 260), (21, 238), (10, 497)]
    (codeMat 501) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane408UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 430), (129, 276), (65, 16), (34, 437), (21, 79), (10, 436)]
    (codeMat 426) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane408UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 256), (160, 162), (68, 69), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane408UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 287), (132, 483), (66, 404), (38, 284), (22, 227), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane408UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (128, 16), (80, 160), (33, 68), (8, 256), (4, 1), (2, 8)]
    (codeMat 161) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane408UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [257, 129, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 168), (129, 280), (80, 252), (33, 186), (9, 511), (4, 16), (3, 24)]
    (codeMat 335) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
