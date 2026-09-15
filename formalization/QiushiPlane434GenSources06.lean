import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0060 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 414), (132, 373), (66, 227), (36, 360), (16, 3), (12, 362), (1, 511)]
    (codeMat 482) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane434GenSource0061 :
    QuotientRankAtLeast (spanCodes [266, 138, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 230), (138, 228), (64, 3), (34, 416), (16, 256), (6, 16), (1, 24)]
    (codeMat 140) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane434GenSource0062 :
    QuotientRankAtLeast (spanCodes [266, 136, 72, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 163), (136, 324), (72, 1), (42, 160), (16, 256), (4, 24), (1, 8)]
    (codeMat 142) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
