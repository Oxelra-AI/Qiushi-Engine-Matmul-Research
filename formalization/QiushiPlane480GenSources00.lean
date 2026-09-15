import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit417From279
import QiushiPlane419GenFinal
import QiushiPlane427GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0000 :
    QuotientRankAtLeast (spanCodes [16, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [16, 10, 1] [(16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit417_lb17_mono

theorem plane480GenSource0001 :
    QuotientRankAtLeast (spanCodes [16, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(16, 32), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0002 :
    QuotientRankAtLeast (spanCodes [16, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(16, 32), (14, 10), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0003 :
    QuotientRankAtLeast (spanCodes [34, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(34, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0004 :
    QuotientRankAtLeast (spanCodes [36, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(36, 36), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0005 :
    QuotientRankAtLeast (spanCodes [38, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(38, 37), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0006 :
    QuotientRankAtLeast (spanCodes [42, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(42, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0007 :
    QuotientRankAtLeast (spanCodes [44, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(44, 52), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0008 :
    QuotientRankAtLeast (spanCodes [46, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(46, 53), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane480GenSource0009 :
    QuotientRankAtLeast (spanCodes [66, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(66, 10), (16, 32), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

end QiushiMatmul
