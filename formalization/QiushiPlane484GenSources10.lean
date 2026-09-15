import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit446From373
import QiushiPlane282GenFinal
import QiushiStep107Orbit373Extraction
import QiushiWcOrbit281Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0100 :
    QuotientRankAtLeast (spanCodes [261, 103, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(261, 301), (103, 460), (19, 312), (10, 224)]
    (codeMat 94) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane484GenSource0101 :
    QuotientRankAtLeast (spanCodes [359, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(359, 401), (19, 304), (10, 400)]
    (codeMat 87) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0102 :
    QuotientRankAtLeast (spanCodes [384, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(384, 1), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0103 :
    QuotientRankAtLeast (spanCodes [390, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(390, 1), (19, 400), (10, 160)]
    (codeMat 85) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0104 :
    QuotientRankAtLeast (spanCodes [257, 162, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(257, 245), (162, 300), (19, 472), (10, 312)]
    (codeMat 214) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane484GenSource0105 :
    QuotientRankAtLeast (spanCodes [448, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(448, 1), (19, 160), (10, 304)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0106 :
    QuotientRankAtLeast (spanCodes [455, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(455, 1), (19, 160), (10, 304)]
    (codeMat 85) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0107 :
    QuotientRankAtLeast (spanCodes [484, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(484, 265), (18, 27), (10, 26), (1, 16)]
    (codeMat 458) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane484GenSource0108 :
    QuotientRankAtLeast (spanCodes [256, 18, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane484GenSource0109 :
    QuotientRankAtLeast (spanCodes [256, 17, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 256), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

end QiushiMatmul
