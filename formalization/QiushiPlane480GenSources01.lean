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

theorem plane480GenSource0010 :
    QuotientRankAtLeast (spanCodes [68, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(68, 10), (16, 256), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed424_lb17

theorem plane480GenSource0011 :
    QuotientRankAtLeast (spanCodes [70, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(70, 10), (16, 256), (1, 1)]
    (codeMat 161) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed424_lb17

theorem plane480GenSource0012 :
    QuotientRankAtLeast (spanCodes [74, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(74, 10), (16, 32), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane480GenSource0013 :
    QuotientRankAtLeast (spanCodes [76, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(76, 10), (16, 256), (1, 1)]
    (codeMat 177) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed424_lb17

theorem plane480GenSource0014 :
    QuotientRankAtLeast (spanCodes [78, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(78, 10), (16, 256), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.line480_seed424_lb17

theorem plane480GenSource0015 :
    QuotientRankAtLeast (spanCodes [96, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(96, 96), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane480GenSource0016 :
    QuotientRankAtLeast (spanCodes [98, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [98, 16, 1] [(98, 98), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane429Gen_lb17

theorem plane480GenSource0017 :
    QuotientRankAtLeast (spanCodes [100, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0018 :
    QuotientRankAtLeast (spanCodes [102, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [100, 16, 1] [(102, 116), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane430Gen_lb17

theorem plane480GenSource0019 :
    QuotientRankAtLeast (spanCodes [104, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(104, 96), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

end QiushiMatmul
