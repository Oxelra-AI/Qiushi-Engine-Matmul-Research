import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiLine480Seeds
import QiushiPlane430GenFinal
import QiushiPlane433GenFinal
import QiushiPlane434GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0050 :
    QuotientRankAtLeast (spanCodes [234, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(234, 116), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0051 :
    QuotientRankAtLeast (spanCodes [236, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(236, 244), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed431_lb17

theorem plane480GenSource0052 :
    QuotientRankAtLeast (spanCodes [238, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(238, 245), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed431_lb17

theorem plane480GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(258, 258), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0054 :
    QuotientRankAtLeast (spanCodes [262, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(262, 258), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0055 :
    QuotientRankAtLeast (spanCodes [264, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(264, 258), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0056 :
    QuotientRankAtLeast (spanCodes [266, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(266, 266), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0057 :
    QuotientRankAtLeast (spanCodes [268, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(268, 258), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0058 :
    QuotientRankAtLeast (spanCodes [270, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(270, 266), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane480GenSource0059 :
    QuotientRankAtLeast (spanCodes [290, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(290, 258), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

end QiushiMatmul
