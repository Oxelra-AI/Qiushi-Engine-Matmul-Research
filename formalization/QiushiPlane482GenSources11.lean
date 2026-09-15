import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0110 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 3), (68, 68), (38, 424), (16, 24), (14, 416), (1, 256)]
    (codeMat 85) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0111 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 22, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (130, 325), (66, 324), (32, 24), (22, 424), (14, 416), (1, 256)]
    (codeMat 84) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0112 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 36, 22, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (128, 325), (66, 68), (36, 16), (22, 168), (12, 416), (1, 256)]
    (codeMat 93) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0113 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 36, 22, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (130, 325), (66, 324), (36, 16), (22, 168), (12, 416), (1, 256)]
    (codeMat 92) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0114 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 36, 18, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (130, 3), (70, 324), (36, 16), (18, 24), (12, 416), (1, 256)]
    (codeMat 93) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0115 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 32, 22, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (128, 325), (66, 68), (32, 24), (22, 424), (14, 416), (1, 256)]
    (codeMat 85) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0116 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 38, 22, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 325), (66, 324), (38, 184), (22, 168), (14, 160), (1, 256)]
    (codeMat 84) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0117 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 3), (68, 68), (32, 8), (16, 24), (14, 160), (1, 256)]
    (codeMat 84) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
