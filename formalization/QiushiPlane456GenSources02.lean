import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0020 :
    QuotientRankAtLeast (spanCodes [290, 161, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(290, 349), (161, 342), (97, 343), (20, 316), (10, 291)]
    (codeMat 236) (codeMat 478) (codeMat 445) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane456GenSource0021 :
    QuotientRankAtLeast (spanCodes [295, 161, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(295, 316), (161, 317), (100, 310), (20, 435), (10, 408)]
    (codeMat 485) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane456GenSource0022 :
    QuotientRankAtLeast (spanCodes [261, 161, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(261, 11), (161, 239), (65, 1), (20, 284), (10, 97)]
    (codeMat 461) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0023 :
    QuotientRankAtLeast (spanCodes [293, 161, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(293, 252), (161, 370), (97, 371), (20, 495), (10, 21)]
    (codeMat 412) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane456GenSource0024 :
    QuotientRankAtLeast (spanCodes [294, 161, 98, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(294, 430), (161, 443), (98, 442), (20, 232), (10, 136)]
    (codeMat 205) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane456GenSource0025 :
    QuotientRankAtLeast (spanCodes [321, 161, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(321, 284), (161, 165), (17, 10), (10, 11), (5, 32)]
    (codeMat 459) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane456GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 161, 66, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(260, 432), (161, 142), (66, 96), (20, 308), (10, 97)]
    (codeMat 270) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane456GenSource0027 :
    QuotientRankAtLeast (spanCodes [257, 161, 70, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(257, 400), (161, 106), (70, 96), (20, 383), (10, 228)]
    (codeMat 110) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane456GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 161, 69, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 343), (161, 142), (69, 238), (20, 466), (10, 228)]
    (codeMat 254) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456GenSource0029 :
    QuotientRankAtLeast (spanCodes [290, 161, 101, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(290, 137), (161, 117), (101, 398), (20, 411), (10, 232)]
    (codeMat 318) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

end QiushiMatmul
