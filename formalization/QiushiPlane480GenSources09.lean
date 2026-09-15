import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiPlane433GenFinal
import QiushiPlane434GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0090 :
    QuotientRankAtLeast (spanCodes [452, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(452, 259), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0091 :
    QuotientRankAtLeast (spanCodes [456, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(456, 258), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0092 :
    QuotientRankAtLeast (spanCodes [458, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(458, 266), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0093 :
    QuotientRankAtLeast (spanCodes [460, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(460, 282), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0094 :
    QuotientRankAtLeast (spanCodes [462, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(462, 274), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0095 :
    QuotientRankAtLeast (spanCodes [480, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(480, 259), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0096 :
    QuotientRankAtLeast (spanCodes [482, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(482, 267), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0097 :
    QuotientRankAtLeast (spanCodes [484, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(484, 283), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0098 :
    QuotientRankAtLeast (spanCodes [486, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(486, 275), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0099 :
    QuotientRankAtLeast (spanCodes [490, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(490, 274), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

end QiushiMatmul
