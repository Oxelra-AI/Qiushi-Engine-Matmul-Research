import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiLine480Seeds
import QiushiPlane427GenFinal
import QiushiPlane430GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0040 :
    QuotientRankAtLeast (spanCodes [198, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(198, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0041 :
    QuotientRankAtLeast (spanCodes [200, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(200, 17), (16, 16), (1, 36)]
    (codeMat 86) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0042 :
    QuotientRankAtLeast (spanCodes [202, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(202, 53), (16, 16), (1, 36)]
    (codeMat 87) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0043 :
    QuotientRankAtLeast (spanCodes [204, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(204, 116), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0044 :
    QuotientRankAtLeast (spanCodes [206, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(206, 116), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0045 :
    QuotientRankAtLeast (spanCodes [224, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(224, 100), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0046 :
    QuotientRankAtLeast (spanCodes [226, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(226, 116), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0047 :
    QuotientRankAtLeast (spanCodes [228, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(228, 228), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed431_lb17

theorem plane480GenSource0048 :
    QuotientRankAtLeast (spanCodes [230, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(230, 229), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed431_lb17

theorem plane480GenSource0049 :
    QuotientRankAtLeast (spanCodes [232, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(232, 100), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

end QiushiMatmul
