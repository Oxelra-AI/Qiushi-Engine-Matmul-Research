import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiPlane255GenFinal
import QiushiPlane267GenFinal
import QiushiPlane269GenFinal
import QiushiPlane433GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0100 :
    QuotientRankAtLeast (spanCodes [492, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 1] [(492, 275), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane433Gen_lb17

theorem plane480GenSource0101 :
    QuotientRankAtLeast (spanCodes [68, 16, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 8, 2, 1] [(68, 96), (16, 2), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane255Gen_lb16

theorem plane480GenSource0102 :
    QuotientRankAtLeast (spanCodes [68, 16, 8, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 8, 2, 1] [(68, 96), (16, 2), (8, 1), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane255Gen_lb16

theorem plane480GenSource0103 :
    QuotientRankAtLeast (spanCodes [64, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(64, 2), (34, 264), (16, 32), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane480GenSource0104 :
    QuotientRankAtLeast (spanCodes [66, 32, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(66, 264), (32, 2), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane480GenSource0105 :
    QuotientRankAtLeast (spanCodes [72, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(72, 2), (42, 264), (16, 32), (1, 1)]
    (codeMat 177) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane480GenSource0106 :
    QuotientRankAtLeast (spanCodes [74, 40, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(74, 264), (40, 2), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane480GenSource0107 :
    QuotientRankAtLeast (spanCodes [98, 16, 6, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(98, 116), (16, 32), (6, 2), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane480GenSource0108 :
    QuotientRankAtLeast (spanCodes [98, 16, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(98, 84), (16, 32), (4, 2), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane480GenSource0109 :
    QuotientRankAtLeast (spanCodes [128, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(128, 2), (16, 1), (12, 264), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

end QiushiMatmul
