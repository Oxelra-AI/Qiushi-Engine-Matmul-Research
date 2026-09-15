import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0000 :
    QuotientRankAtLeast (spanCodes [450, 37, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(450, 109), (37, 20), (20, 30), (10, 61)]
    (codeMat 275) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane458GenSource0001 :
    QuotientRankAtLeast (spanCodes [389, 71, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(389, 20), (71, 10), (20, 322), (10, 68)]
    (codeMat 233) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane458GenSource0002 :
    QuotientRankAtLeast (spanCodes [416, 98, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(416, 10), (98, 106), (20, 153), (10, 126)]
    (codeMat 358) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane458GenSource0003 :
    QuotientRankAtLeast (spanCodes [321, 131, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(321, 20), (131, 10), (20, 231), (10, 153)]
    (codeMat 428) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane458GenSource0004 :
    QuotientRankAtLeast (spanCodes [356, 166, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(356, 78), (166, 20), (20, 262), (10, 322)]
    (codeMat 179) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane458GenSource0005 :
    QuotientRankAtLeast (spanCodes [262, 196, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(262, 328), (196, 80), (20, 68), (10, 262)]
    (codeMat 98) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane458GenSource0006 :
    QuotientRankAtLeast (spanCodes [291, 225, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(291, 243), (225, 116), (20, 126), (10, 231)]
    (codeMat 309) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane458GenSource0007 :
    QuotientRankAtLeast (spanCodes [390, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(390, 288), (68, 79), (20, 20), (10, 11), (1, 1)]
    (codeMat 409) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane458GenSource0008 :
    QuotientRankAtLeast (spanCodes [388, 69, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(388, 133), (69, 263), (20, 42), (9, 32), (3, 1)]
    (codeMat 345) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane458GenSource0009 :
    QuotientRankAtLeast (spanCodes [418, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(418, 276), (96, 126), (20, 20), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
