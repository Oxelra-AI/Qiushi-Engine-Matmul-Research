import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiPlane433GenFinal
import QiushiPlane434GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0080 :
    QuotientRankAtLeast (spanCodes [394, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(394, 266), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0081 :
    QuotientRankAtLeast (spanCodes [396, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(396, 266), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0082 :
    QuotientRankAtLeast (spanCodes [398, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(398, 258), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0083 :
    QuotientRankAtLeast (spanCodes [418, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(418, 274), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0084 :
    QuotientRankAtLeast (spanCodes [420, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(420, 274), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0085 :
    QuotientRankAtLeast (spanCodes [424, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(424, 259), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0086 :
    QuotientRankAtLeast (spanCodes [426, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(426, 267), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0087 :
    QuotientRankAtLeast (spanCodes [428, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(428, 267), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0088 :
    QuotientRankAtLeast (spanCodes [430, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(430, 259), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0089 :
    QuotientRankAtLeast (spanCodes [450, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(450, 258), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

end QiushiMatmul
