import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit183Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0040 :
    QuotientRankAtLeast (spanCodes [276, 84, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(276, 479), (84, 95), (48, 32), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane473GenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 70, 39, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 411), (70, 493), (39, 34), (18, 3), (10, 35)]
    (codeMat 275) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane473GenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 84, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(272, 469), (84, 84), (52, 42), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane473GenSource0043 :
    QuotientRankAtLeast (spanCodes [292, 130, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 384), (130, 32), (84, 85), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane473GenSource0044 :
    QuotientRankAtLeast (spanCodes [292, 134, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(292, 128), (134, 246), (66, 30), (22, 255), (10, 31), (1, 3)]
    (codeMat 190) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0045 :
    QuotientRankAtLeast (spanCodes [293, 133, 65, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(293, 22), (133, 105), (65, 130), (21, 96), (8, 128), (2, 8)]
    (codeMat 143) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0046 :
    QuotientRankAtLeast (spanCodes [293, 133, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(293, 22), (133, 227), (64, 130), (20, 232), (9, 128), (3, 8)]
    (codeMat 207) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0047 :
    QuotientRankAtLeast (spanCodes [292, 148, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 511), (148, 127), (84, 95), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane473GenSource0048 :
    QuotientRankAtLeast (spanCodes [293, 133, 70, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(293, 119), (133, 408), (70, 411), (18, 32), (10, 34)]
    (codeMat 215) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane473GenSource0049 :
    QuotientRankAtLeast (spanCodes [293, 148, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(293, 440), (148, 119), (84, 117), (9, 32), (3, 1)]
    (codeMat 225) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
