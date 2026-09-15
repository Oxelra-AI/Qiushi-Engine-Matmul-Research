import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiStep133Mono397From243
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0010 :
    QuotientRankAtLeast (spanCodes [293, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(293, 10), (180, 126), (68, 147), (10, 135)]
    (codeMat 185) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0011 :
    QuotientRankAtLeast (spanCodes [305, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(305, 116), (180, 237), (68, 147), (10, 135)]
    (codeMat 460) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0012 :
    QuotientRankAtLeast (spanCodes [310, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(310, 231), (180, 126), (68, 147), (10, 135)]
    (codeMat 461) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane464GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 180, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 326), (180, 349), (68, 69), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane464GenSource0014 :
    QuotientRankAtLeast (spanCodes [259, 177, 65, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 42), (177, 425), (65, 32), (10, 295), (5, 1)]
    (codeMat 425) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane464GenSource0015 :
    QuotientRankAtLeast (spanCodes [261, 165, 68, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(261, 475), (165, 142), (68, 228), (17, 11), (10, 10)]
    (codeMat 339) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane464GenSource0016 :
    QuotientRankAtLeast (spanCodes [261, 164, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(261, 319), (164, 96), (68, 228), (16, 1), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane464GenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 163, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(256, 1), (163, 106), (68, 10), (23, 466), (10, 228)]
    (codeMat 236) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane464GenSource0018 :
    QuotientRankAtLeast (spanCodes [257, 162, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(257, 11), (162, 132), (68, 10), (22, 310), (10, 228)]
    (codeMat 165) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane464GenSource0019 :
    QuotientRankAtLeast (spanCodes [263, 164, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(263, 310), (164, 96), (68, 228), (16, 1), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

end QiushiMatmul
