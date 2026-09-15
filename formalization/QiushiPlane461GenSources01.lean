import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0010 :
    QuotientRankAtLeast (spanCodes [263, 148, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(263, 430), (148, 20), (68, 232), (54, 1), (10, 462)]
    (codeMat 443) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane461GenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 35, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 274), (129, 502), (68, 191), (35, 80), (23, 240), (10, 440)]
    (codeMat 86) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane461GenSource0012 :
    QuotientRankAtLeast (spanCodes [259, 134, 68, 36, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(259, 328), (134, 440), (68, 80), (36, 1), (21, 263), (10, 322)]
    (codeMat 99) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane461GenSource0013 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 35, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 160), (129, 240), (68, 280), (35, 68), (22, 262), (10, 323)]
    (codeMat 99) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane461GenSource0014 :
    QuotientRankAtLeast (spanCodes [262, 144, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(262, 418), (144, 32), (68, 175), (50, 294), (10, 295)]
    (codeMat 498) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane461GenSource0015 :
    QuotientRankAtLeast (spanCodes [275, 133, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(275, 142), (133, 42), (68, 133), (39, 440), (10, 441)]
    (codeMat 491) (codeMat 339) (codeMat 467) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane461GenSource0016 :
    QuotientRankAtLeast (spanCodes [278, 128, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(278, 164), (128, 32), (68, 392), (34, 294), (10, 295)]
    (codeMat 354) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane461GenSource0017 :
    QuotientRankAtLeast (spanCodes [292, 162, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(292, 27), (162, 11), (68, 280), (16, 1), (10, 79)]
    (codeMat 298) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane461GenSource0018 :
    QuotientRankAtLeast (spanCodes [256, 151, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (151, 408), (68, 10), (53, 284), (10, 228)]
    (codeMat 172) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane461GenSource0019 :
    QuotientRankAtLeast (spanCodes [257, 150, 68, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(257, 11), (150, 278), (68, 10), (52, 402), (10, 228)]
    (codeMat 165) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
