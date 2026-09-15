import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0100 :
    QuotientRankAtLeast (spanCodes [256, 100, 8, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 256), (100, 96), (8, 9), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane425GenSource0101 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 46), (144, 438), (80, 406), (10, 132), (6, 3), (1, 2)]
    (codeMat 225) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane425GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 44), (128, 32), (80, 272), (10, 132), (6, 1), (1, 2)]
    (codeMat 161) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane425GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 144, 84, 36, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 127), (144, 1), (84, 403), (36, 390), (10, 97), (1, 365)]
    (codeMat 342) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 128, 84, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 97), (128, 365), (84, 159), (52, 269), (10, 371), (1, 390)]
    (codeMat 431) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0105 :
    QuotientRankAtLeast (spanCodes [258, 132, 86, 48, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 15), (132, 14), (86, 419), (48, 2), (10, 173), (1, 511)]
    (codeMat 405) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane425GenSource0106 :
    QuotientRankAtLeast (spanCodes [258, 128, 86, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(258, 347), (128, 192), (86, 181), (52, 222), (10, 507), (1, 292)]
    (codeMat 307) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane425GenSource0107 :
    QuotientRankAtLeast (spanCodes [258, 128, 86, 50, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 97), (128, 365), (86, 159), (50, 269), (10, 245), (1, 390)]
    (codeMat 494) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 150, 84, 36, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 148), (150, 402), (84, 254), (36, 390), (10, 268), (1, 365)]
    (codeMat 405) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 134, 84, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 349), (134, 243), (84, 419), (52, 429), (10, 338), (1, 511)]
    (codeMat 230) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

end QiushiMatmul
