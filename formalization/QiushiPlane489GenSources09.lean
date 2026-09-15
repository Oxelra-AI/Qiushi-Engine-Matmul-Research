import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane282GenFinal
import QiushiPlane433GenFinal
import QiushiPlane457GenFinal
import QiushiPlane462GenFinal
import QiushiPlane466GenFinal
import QiushiPlane470GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0090 :
    QuotientRankAtLeast (spanCodes [258, 242, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 479), (242, 459), (10, 449)]
    (codeMat 226) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane489GenSource0091 :
    QuotientRankAtLeast (spanCodes [258, 243, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 10), (243, 78), (10, 383)]
    (codeMat 229) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0092 :
    QuotientRankAtLeast (spanCodes [258, 244, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 343), (244, 84), (10, 10)]
    (codeMat 467) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0093 :
    QuotientRankAtLeast (spanCodes [258, 245, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [178, 68, 10] [(258, 68), (245, 10), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane462Gen_lb18

theorem plane489GenSource0094 :
    QuotientRankAtLeast (spanCodes [258, 246, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 315), (246, 10), (10, 68)]
    (codeMat 187) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0095 :
    QuotientRankAtLeast (spanCodes [257, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(257, 258), (9, 16), (3, 1)]
    (codeMat 281) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0096 :
    QuotientRankAtLeast (spanCodes [258, 10, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 17), (10, 259), (6, 1)]
    (codeMat 169) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0097 :
    QuotientRankAtLeast (spanCodes [258, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 274), (18, 16), (10, 17)]
    (codeMat 282) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane489GenSource0098 :
    QuotientRankAtLeast (spanCodes [257, 16, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(257, 280), (16, 1), (9, 27), (3, 16)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane489GenSource0099 :
    QuotientRankAtLeast (spanCodes [258, 18, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 280), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

end QiushiMatmul
