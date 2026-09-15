import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiLine480Seeds
import QiushiPlane419GenFinal
import QiushiPlane428GenFinal
import QiushiPlane429GenFinal
import QiushiPlane430GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0020 :
    QuotientRankAtLeast (spanCodes [106, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [98, 16, 1] [(106, 98), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane429Gen_lb17

theorem plane480GenSource0021 :
    QuotientRankAtLeast (spanCodes [108, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(108, 101), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0022 :
    QuotientRankAtLeast (spanCodes [110, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(110, 117), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0023 :
    QuotientRankAtLeast (spanCodes [132, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(132, 96), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane480GenSource0024 :
    QuotientRankAtLeast (spanCodes [134, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(134, 96), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane480GenSource0025 :
    QuotientRankAtLeast (spanCodes [136, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(136, 10), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0026 :
    QuotientRankAtLeast (spanCodes [138, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(138, 10), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0027 :
    QuotientRankAtLeast (spanCodes [140, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [98, 16, 1] [(140, 98), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane429Gen_lb17

theorem plane480GenSource0028 :
    QuotientRankAtLeast (spanCodes [142, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [98, 16, 1] [(142, 98), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane429Gen_lb17

theorem plane480GenSource0029 :
    QuotientRankAtLeast (spanCodes [160, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(160, 10), (16, 1), (1, 256)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed424_lb17

end QiushiMatmul
