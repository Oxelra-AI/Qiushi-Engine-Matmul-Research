import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiBranch262Extraction
import QiushiBranch416Extraction
import QiushiMonoOrbit412From262
import QiushiMonoOrbit414From262
import QiushiStep138Orbit435AuditedAlias
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0000 :
    QuotientRankAtLeast (spanCodes [20, 2, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [12, 2, 1] [(20, 12), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit412_lb17_mono

theorem plane481GenSource0001 :
    QuotientRankAtLeast (spanCodes [20, 8, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 2] [(20, 272), (8, 2), (1, 4)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit414_lb17_mono

theorem plane481GenSource0002 :
    QuotientRankAtLeast (spanCodes [38, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [193, 19, 10] [(38, 25), (20, 19), (1, 216)]
    (codeMat 275) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step138_orbit435_span193_19_10_lb17

theorem plane481GenSource0003 :
    QuotientRankAtLeast (spanCodes [46, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [193, 19, 10] [(46, 210), (20, 193), (1, 216)]
    (codeMat 275) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step138_orbit435_span193_19_10_lb17

theorem plane481GenSource0004 :
    QuotientRankAtLeast (spanCodes [64, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(64, 1), (20, 272), (1, 4)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane481GenSource0005 :
    QuotientRankAtLeast (spanCodes [68, 20, 2, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 12, 2, 1] [(68, 12), (20, 132), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit262_lb17

theorem plane481GenSource0006 :
    QuotientRankAtLeast (spanCodes [72, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(72, 1), (20, 272), (1, 4)]
    (codeMat 86) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane481GenSource0007 :
    QuotientRankAtLeast (spanCodes [68, 20, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 79), (20, 43), (14, 10), (1, 1)]
    (codeMat 409) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0008 :
    QuotientRankAtLeast (spanCodes [70, 20, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(70, 79), (20, 42), (12, 10), (1, 1)]
    (codeMat 401) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0009 :
    QuotientRankAtLeast (spanCodes [66, 20, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(66, 69), (20, 43), (14, 10), (1, 1)]
    (codeMat 281) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

end QiushiMatmul
