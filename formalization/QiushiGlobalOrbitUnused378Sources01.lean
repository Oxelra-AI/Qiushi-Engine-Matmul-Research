import QiushiGlobalOrbitUnused378Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiStep99Orbit217Dispatch
import QiushiStep99Orbit237Dispatch
import QiushiWcOrbit241Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane378UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [290, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 136, 96, 20, 1] [(290, 387), (162, 386), (68, 136), (19, 287), (10, 483)]
    (codeMat 172) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit237_lb16_unconditional

theorem plane378UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [291, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 136, 96, 20, 1] [(291, 362), (162, 386), (68, 136), (19, 252), (10, 483)]
    (codeMat 359) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit237_lb16_unconditional

theorem plane378UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [292, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(292, 1), (162, 433), (68, 132), (19, 475), (10, 228)]
    (codeMat 103) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane378UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [293, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 162, 68, 19, 10] [(293, 341), (162, 245), (68, 162), (19, 25), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit241_lb16_wc

theorem plane378UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [294, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(294, 308), (162, 341), (68, 96), (19, 475), (10, 228)]
    (codeMat 124) (codeMat 242) (codeMat 205) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane378UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [295, 162, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 162, 68, 19, 10] [(295, 258), (162, 255), (68, 168), (19, 25), (10, 10)]
    (codeMat 459) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit241_lb16_wc

theorem plane378UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [128, 64, 32, 16, 8, 4, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(128, 130), (64, 65), (32, 32), (16, 16), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_1

end QiushiMatmul
