import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0030 :
    QuotientRankAtLeast (spanCodes [291, 161, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(291, 505), (161, 107), (100, 381), (20, 374), (10, 408)]
    (codeMat 358) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0031 :
    QuotientRankAtLeast (spanCodes [288, 161, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(288, 504), (161, 499), (64, 1), (20, 278), (10, 132)]
    (codeMat 204) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0032 :
    QuotientRankAtLeast (spanCodes [292, 161, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(292, 1), (161, 239), (68, 441), (20, 97), (10, 316)]
    (codeMat 407) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456GenSource0033 :
    QuotientRankAtLeast (spanCodes [322, 131, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(322, 278), (131, 175), (34, 10), (20, 11), (10, 42)]
    (codeMat 467) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane456GenSource0034 :
    QuotientRankAtLeast (spanCodes [323, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(323, 269), (130, 1), (35, 160), (20, 262), (10, 434)]
    (codeMat 93) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane456GenSource0035 :
    QuotientRankAtLeast (spanCodes [262, 130, 69, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 68), (130, 1), (69, 263), (35, 160), (20, 328), (10, 440)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane456GenSource0036 :
    QuotientRankAtLeast (spanCodes [326, 134, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(326, 264), (134, 280), (39, 327), (20, 259), (10, 326)]
    (codeMat 99) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane456GenSource0037 :
    QuotientRankAtLeast (spanCodes [257, 161, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(257, 137), (161, 431), (99, 116), (20, 306), (10, 252)]
    (codeMat 382) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane456GenSource0038 :
    QuotientRankAtLeast (spanCodes [293, 161, 71, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(293, 11), (161, 473), (71, 228), (20, 343), (10, 238)]
    (codeMat 318) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456GenSource0039 :
    QuotientRankAtLeast (spanCodes [294, 161, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(294, 136), (161, 339), (68, 295), (20, 232), (10, 430)]
    (codeMat 382) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

end QiushiMatmul
