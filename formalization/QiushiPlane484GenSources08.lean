import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit417From279
import QiushiStep104Orbit279Split
import QiushiStep132Orbit451AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0080 :
    QuotientRankAtLeast (spanCodes [483, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(483, 274), (19, 19), (10, 25)]
    (codeMat 394) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane484GenSource0081 :
    QuotientRankAtLeast (spanCodes [484, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(484, 274), (19, 19), (10, 25)]
    (codeMat 458) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane484GenSource0082 :
    QuotientRankAtLeast (spanCodes [485, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(485, 267), (19, 25), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane484GenSource0083 :
    QuotientRankAtLeast (spanCodes [487, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(487, 257), (19, 10), (10, 19)]
    (codeMat 458) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane484GenSource0084 :
    QuotientRankAtLeast (spanCodes [18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [16, 10, 1] [(18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit417_lb17_mono

theorem plane484GenSource0085 :
    QuotientRankAtLeast (spanCodes [17, 8, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [16, 10, 1] [(17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit417_lb17_mono

theorem plane484GenSource0086 :
    QuotientRankAtLeast (spanCodes [16, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [16, 10, 1] [(16, 1), (9, 27), (3, 16)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit417_lb17_mono

theorem plane484GenSource0087 :
    QuotientRankAtLeast (spanCodes [68, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(68, 68), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane484GenSource0088 :
    QuotientRankAtLeast (spanCodes [70, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(70, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

theorem plane484GenSource0089 :
    QuotientRankAtLeast (spanCodes [96, 17, 8, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(96, 68), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step104_orbit279_lb17

end QiushiMatmul
