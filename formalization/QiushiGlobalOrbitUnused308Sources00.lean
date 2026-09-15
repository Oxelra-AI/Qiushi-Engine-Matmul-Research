import QiushiGlobalOrbitUnused308Data
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiPlane298GenBindings00
import QiushiStep99Orbit120Dispatch
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane308UnusedGenSource0000 :
    QuotientRankAtLeast (spanCodes [288, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(288, 32), (96, 34), (10, 118), (4, 8), (1, 9)]
    (codeMat 417) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane308UnusedGenSource0001 :
    QuotientRankAtLeast (spanCodes [288, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(288, 288), (96, 96), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane308UnusedGenSource0002 :
    QuotientRankAtLeast (spanCodes [288, 96, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(288, 288), (96, 96), (22, 31), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane308UnusedGenSource0003 :
    QuotientRankAtLeast (spanCodes [256, 64, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 8), (64, 1), (32, 32), (10, 132), (1, 2)]
    (codeMat 140) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane308UnusedGenSource0004 :
    QuotientRankAtLeast (spanCodes [258, 66, 34, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 173), (66, 133), (34, 164), (10, 132), (1, 2)]
    (codeMat 142) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane308UnusedGenSource0005 :
    QuotientRankAtLeast (spanCodes [260, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(260, 1), (68, 44), (36, 2), (10, 304), (1, 32)]
    (codeMat 93) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane308UnusedGenSource0006 :
    QuotientRankAtLeast (spanCodes [262, 70, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(262, 319), (70, 316), (38, 274), (10, 304), (1, 32)]
    (codeMat 95) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane308UnusedGenSource0007 :
    QuotientRankAtLeast (spanCodes [276, 84, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(276, 469), (84, 85), (52, 42), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298GenBound0004

theorem plane308UnusedGenSource0008 :
    QuotientRankAtLeast (spanCodes [278, 86, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(278, 479), (86, 95), (54, 32), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298GenBound0004

theorem plane308UnusedGenSource0009 :
    QuotientRankAtLeast (spanCodes [288, 130, 96, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(288, 448), (130, 32), (96, 133), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

end QiushiMatmul
