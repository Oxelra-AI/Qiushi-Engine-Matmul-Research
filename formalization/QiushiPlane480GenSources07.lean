import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiPlane433GenFinal
import QiushiPlane434GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0070 :
    QuotientRankAtLeast (spanCodes [334, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(334, 282), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0071 :
    QuotientRankAtLeast (spanCodes [352, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(352, 258), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0072 :
    QuotientRankAtLeast (spanCodes [354, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(354, 266), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0073 :
    QuotientRankAtLeast (spanCodes [356, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(356, 274), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0074 :
    QuotientRankAtLeast (spanCodes [358, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(358, 282), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0075 :
    QuotientRankAtLeast (spanCodes [362, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(362, 258), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0076 :
    QuotientRankAtLeast (spanCodes [366, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(366, 259), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0077 :
    QuotientRankAtLeast (spanCodes [386, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(386, 258), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0078 :
    QuotientRankAtLeast (spanCodes [388, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(388, 258), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0079 :
    QuotientRankAtLeast (spanCodes [392, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(392, 258), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

end QiushiMatmul
