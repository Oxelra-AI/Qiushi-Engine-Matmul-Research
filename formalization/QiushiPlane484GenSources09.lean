import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit446From373
import QiushiStep104Orbit279Split
import QiushiStep107Orbit373Extraction
import QiushiStep138Orbit435AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0090 :
    QuotientRankAtLeast (spanCodes [101, 16, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(101, 78), (16, 27), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane484GenSource0091 :
    QuotientRankAtLeast (spanCodes [193, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [193, 19, 10] [(193, 193), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step138_orbit435_span193_19_10_lb17

theorem plane484GenSource0092 :
    QuotientRankAtLeast (spanCodes [256, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(256, 1), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0093 :
    QuotientRankAtLeast (spanCodes [260, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(260, 1), (19, 400), (10, 160)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0094 :
    QuotientRankAtLeast (spanCodes [288, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(288, 1), (19, 400), (10, 160)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0095 :
    QuotientRankAtLeast (spanCodes [292, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(292, 1), (19, 400), (10, 160)]
    (codeMat 87) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0096 :
    QuotientRankAtLeast (spanCodes [320, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(320, 1), (19, 304), (10, 400)]
    (codeMat 84) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0097 :
    QuotientRankAtLeast (spanCodes [262, 70, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(262, 21), (70, 20), (19, 472), (10, 312)]
    (codeMat 140) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane484GenSource0098 :
    QuotientRankAtLeast (spanCodes [354, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(354, 401), (19, 304), (10, 400)]
    (codeMat 86) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane484GenSource0099 :
    QuotientRankAtLeast (spanCodes [257, 99, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(257, 301), (99, 460), (19, 472), (10, 224)]
    (codeMat 86) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

end QiushiMatmul
