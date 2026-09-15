import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiOrbit41FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0110 :
    QuotientRankAtLeast (spanCodes [260, 160, 98, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(260, 32), (160, 476), (98, 84), (18, 511), (10, 502), (1, 384)]
    (codeMat 111) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane483GenSource0111 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (132, 392), (68, 264), (36, 1), (16, 511), (10, 149), (1, 360)]
    (codeMat 299) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
