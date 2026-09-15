import QiushiPlane276GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit130From35T
import QiushiStep99Orbit144Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane276GenSource0000 :
    QuotientRankAtLeast (spanCodes [272, 180, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(272, 118), (180, 463), (96, 411), (2, 1), (1, 3)]
    (codeMat 169) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane276GenSource0001 :
    QuotientRankAtLeast (spanCodes [272, 92, 60, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(272, 411), (92, 84), (60, 34), (2, 3), (1, 1)]
    (codeMat 281) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane276GenSource0002 :
    QuotientRankAtLeast (spanCodes [272, 140, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(272, 493), (140, 87), (96, 411), (2, 2), (1, 3)]
    (codeMat 185) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane276GenSource0003 :
    QuotientRankAtLeast (spanCodes [272, 128, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(272, 96), (128, 8), (96, 272), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane276GenSource0004 :
    QuotientRankAtLeast (spanCodes [272, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(272, 272), (96, 96), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane276GenSource0005 :
    QuotientRankAtLeast (spanCodes [272, 184, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(272, 368), (184, 280), (96, 272), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane276GenSource0006 :
    QuotientRankAtLeast (spanCodes [272, 68, 36, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 162), (68, 12), (36, 256), (2, 2), (1, 1)]
    (codeMat 225) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane276GenSource0007 :
    QuotientRankAtLeast (spanCodes [272, 164, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 162), (164, 416), (96, 430), (2, 2), (1, 3)]
    (codeMat 481) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane276GenSource0008 :
    QuotientRankAtLeast (spanCodes [260, 96, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(260, 256), (96, 162), (20, 12), (2, 1), (1, 2)]
    (codeMat 337) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane276GenSource0009 :
    QuotientRankAtLeast (spanCodes [272, 148, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 268), (148, 13), (96, 430), (2, 1), (1, 3)]
    (codeMat 369) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

end QiushiMatmul
