import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
import QiushiPlane449GenFinal
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0090 :
    QuotientRankAtLeast (spanCodes [147, 84, 48]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [316, 160, 1] [(147, 316), (84, 161), (48, 1)]
    (codeMat 250) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane449Gen_lb17

theorem plane491GenSource0091 :
    QuotientRankAtLeast (spanCodes [133, 66, 38, 22]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(133, 170), (66, 308), (38, 11), (22, 10)]
    (codeMat 458) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane491GenSource0092 :
    QuotientRankAtLeast (spanCodes [146, 84, 49]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [316, 160, 1] [(146, 1), (84, 412), (49, 160)]
    (codeMat 159) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane449Gen_lb17

theorem plane491GenSource0093 :
    QuotientRankAtLeast (spanCodes [151, 84, 52]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [316, 160, 1] [(151, 316), (84, 317), (52, 160)]
    (codeMat 205) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane449Gen_lb17

theorem plane491GenSource0094 :
    QuotientRankAtLeast (spanCodes [131, 65, 32, 21]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(131, 10), (65, 1), (32, 260), (21, 170)]
    (codeMat 461) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0095 :
    QuotientRankAtLeast (spanCodes [139, 73, 40, 29]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(139, 420), (73, 260), (40, 1), (29, 10)]
    (codeMat 330) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0096 :
    QuotientRankAtLeast (spanCodes [136, 73, 43, 29]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(136, 420), (73, 260), (43, 11), (29, 10)]
    (codeMat 267) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0097 :
    QuotientRankAtLeast (spanCodes [131, 67, 32, 23]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(131, 10), (67, 11), (32, 260), (23, 170)]
    (codeMat 396) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0098 :
    QuotientRankAtLeast (spanCodes [140, 67, 47, 23]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(140, 171), (67, 420), (47, 10), (23, 11)]
    (codeMat 282) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0099 :
    QuotientRankAtLeast (spanCodes [136, 64, 43, 20]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(136, 11), (64, 1), (43, 170), (20, 430)]
    (codeMat 468) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
