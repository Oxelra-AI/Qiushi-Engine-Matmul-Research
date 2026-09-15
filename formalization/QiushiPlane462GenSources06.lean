import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep99Orbit231Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0060 :
    QuotientRankAtLeast (spanCodes [257, 165, 68, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(257, 316), (165, 358), (68, 284), (20, 91), (9, 63), (3, 365)]
    (codeMat 174) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0061 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(256, 32), (164, 52), (68, 284), (21, 91), (9, 63), (3, 365)]
    (codeMat 167) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0062 :
    QuotientRankAtLeast (spanCodes [260, 161, 68, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(260, 16), (161, 114), (68, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane462GenSource0063 :
    QuotientRankAtLeast (spanCodes [260, 148, 68, 38, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(260, 128), (148, 170), (68, 129), (38, 469), (10, 350)]
    (codeMat 372) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane462GenSource0064 :
    QuotientRankAtLeast (spanCodes [261, 148, 68, 37, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(261, 297), (148, 52), (68, 332), (37, 265), (9, 365), (3, 63)]
    (codeMat 183) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0065 :
    QuotientRankAtLeast (spanCodes [260, 147, 68, 33, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(260, 1), (147, 373), (68, 129), (33, 139), (10, 350)]
    (codeMat 309) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane462GenSource0066 :
    QuotientRankAtLeast (spanCodes [276, 130, 68, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(276, 11), (130, 1), (68, 452), (48, 16), (10, 96), (1, 256)]
    (codeMat 85) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0067 :
    QuotientRankAtLeast (spanCodes [288, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 8), (178, 126), (64, 128), (10, 150), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0068 :
    QuotientRankAtLeast (spanCodes [290, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 136), (178, 104), (66, 151), (10, 148), (6, 128), (1, 2)]
    (codeMat 143) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0069 :
    QuotientRankAtLeast (spanCodes [258, 147, 64, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 316), (147, 43), (64, 365), (33, 296), (10, 344), (4, 32)]
    (codeMat 143) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
