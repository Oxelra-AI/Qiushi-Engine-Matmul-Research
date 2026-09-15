import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
import QiushiPlane448GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0090 :
    QuotientRankAtLeast (spanCodes [288, 69, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(288, 260), (69, 160), (17, 11), (10, 10)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0091 :
    QuotientRankAtLeast (spanCodes [291, 68, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(291, 430), (68, 160), (16, 1), (10, 10)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0092 :
    QuotientRankAtLeast (spanCodes [260, 134, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(260, 1), (134, 11), (84, 171), (10, 420)]
    (codeMat 229) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0093 :
    QuotientRankAtLeast (spanCodes [273, 146, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(273, 270), (146, 260), (84, 271), (10, 420)]
    (codeMat 165) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0094 :
    QuotientRankAtLeast (spanCodes [256, 144, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(256, 1), (144, 260), (84, 271), (10, 420)]
    (codeMat 172) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0095 :
    QuotientRankAtLeast (spanCodes [276, 133, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(276, 170), (133, 11), (84, 171), (10, 420)]
    (codeMat 236) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0096 :
    QuotientRankAtLeast (spanCodes [384, 69, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(384, 260), (69, 170), (17, 11), (10, 10)]
    (codeMat 459) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0097 :
    QuotientRankAtLeast (spanCodes [386, 69, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(386, 430), (69, 170), (17, 11), (10, 10)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0098 :
    QuotientRankAtLeast (spanCodes [404, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [314, 160, 1] [(404, 315), (84, 314), (10, 160)]
    (codeMat 140) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane448Gen_lb17

theorem plane487GenSource0099 :
    QuotientRankAtLeast (spanCodes [291, 130, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(291, 10), (130, 260), (84, 171), (10, 420)]
    (codeMat 183) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
