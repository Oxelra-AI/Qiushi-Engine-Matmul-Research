import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0020 :
    QuotientRankAtLeast (spanCodes [260, 160, 8, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(260, 256), (160, 162), (8, 8), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane315GenSource0021 :
    QuotientRankAtLeast (spanCodes [260, 128, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 3), (128, 45), (32, 2), (22, 34), (10, 164), (1, 438)]
    (codeMat 215) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane315GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 160, 70, 18, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(260, 448), (160, 251), (70, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane315GenSource0023 :
    QuotientRankAtLeast (spanCodes [260, 144, 80, 48, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(260, 1), (144, 432), (80, 245), (48, 63), (10, 411), (1, 192)]
    (codeMat 125) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

theorem plane315GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 150, 86, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(260, 1), (150, 96), (86, 486), (54, 365), (10, 274), (1, 128)]
    (codeMat 125) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane315GenSource0025 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 34, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 2), (130, 3), (70, 44), (34, 138), (10, 316), (1, 32)]
    (codeMat 397) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane315GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 130, 82, 34, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 3), (130, 2), (82, 304), (34, 137), (10, 164), (1, 438)]
    (codeMat 253) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane315GenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 134, 86, 38, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(260, 504), (134, 224), (86, 244), (38, 255), (10, 274), (1, 128)]
    (codeMat 102) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane315GenSource0028 :
    QuotientRankAtLeast (spanCodes [260, 134, 70, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 63), (134, 457), (70, 274), (38, 440), (20, 456), (10, 80), (1, 128)]
    (codeMat 87) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane315GenSource0029 :
    QuotientRankAtLeast (spanCodes [260, 160, 98, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(260, 3), (160, 350), (98, 92), (22, 240), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

end QiushiMatmul
