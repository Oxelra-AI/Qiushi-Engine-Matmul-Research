import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit231Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0040 :
    QuotientRankAtLeast (spanCodes [266, 162, 104, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(266, 279), (162, 316), (104, 42), (16, 32), (1, 128)]
    (codeMat 84) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane434GenSource0041 :
    QuotientRankAtLeast (spanCodes [262, 130, 64, 16, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 20), (130, 2), (64, 9), (16, 128), (12, 96), (1, 8)]
    (codeMat 141) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane434GenSource0042 :
    QuotientRankAtLeast (spanCodes [266, 132, 102, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(266, 142), (132, 164), (102, 335), (16, 32), (1, 448)]
    (codeMat 87) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane434GenSource0043 :
    QuotientRankAtLeast (spanCodes [266, 170, 78, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(266, 351), (170, 10), (78, 68), (16, 16), (1, 256)]
    (codeMat 87) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane434GenSource0044 :
    QuotientRankAtLeast (spanCodes [266, 138, 70, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(266, 171), (138, 170), (70, 69), (42, 176), (16, 16), (1, 320)]
    (codeMat 84) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane434GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 128, 96, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (128, 8), (96, 20), (16, 1), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane434GenSource0046 :
    QuotientRankAtLeast (spanCodes [260, 162, 68, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (162, 69), (68, 26), (16, 320), (14, 160), (1, 16)]
    (codeMat 141) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane434GenSource0047 :
    QuotientRankAtLeast (spanCodes [266, 138, 76, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(266, 161), (138, 186), (76, 69), (42, 160), (16, 16), (1, 320)]
    (codeMat 86) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane434GenSource0048 :
    QuotientRankAtLeast (spanCodes [266, 140, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(266, 99), (140, 98), (98, 412), (16, 16), (1, 256)]
    (codeMat 85) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane434GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 34, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 390), (134, 197), (66, 322), (34, 240), (16, 360), (14, 80), (1, 128)]
    (codeMat 92) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
