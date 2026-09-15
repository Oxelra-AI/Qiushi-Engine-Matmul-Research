import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0080 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 31), (134, 28), (68, 252), (32, 9), (16, 8), (10, 104)]
    (codeMat 114) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0081 :
    QuotientRankAtLeast (spanCodes [273, 129, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(273, 474), (129, 464), (82, 170), (49, 475), (10, 191), (6, 192)]
    (codeMat 102) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0082 :
    QuotientRankAtLeast (spanCodes [256, 144, 82, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (144, 3), (82, 252), (32, 8), (10, 224), (6, 128)]
    (codeMat 86) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0083 :
    QuotientRankAtLeast (spanCodes [257, 132, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 11), (132, 20), (64, 1), (39, 191), (20, 420), (10, 127)]
    (codeMat 236) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0084 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 192), (129, 10), (64, 1), (34, 272), (20, 160), (10, 20)]
    (codeMat 140) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0085 :
    QuotientRankAtLeast (spanCodes [293, 164, 68, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(293, 352), (164, 222), (68, 97), (16, 27), (9, 1), (3, 16)]
    (codeMat 395) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane474GenSource0086 :
    QuotientRankAtLeast (spanCodes [292, 181, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 511), (181, 394), (84, 84), (8, 384), (2, 32)]
    (codeMat 93) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane474GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 64, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 138), (64, 1), (36, 32), (20, 406), (10, 132), (1, 2)]
    (codeMat 204) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane474GenSource0088 :
    QuotientRankAtLeast (spanCodes [272, 81, 49, 8, 5, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(272, 408), (81, 284), (49, 44), (8, 32), (5, 2), (2, 3)]
    (codeMat 273) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane474GenSource0089 :
    QuotientRankAtLeast (spanCodes [259, 130, 83, 34, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(259, 437), (130, 2), (83, 133), (34, 138), (10, 170), (7, 438)]
    (codeMat 405) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
