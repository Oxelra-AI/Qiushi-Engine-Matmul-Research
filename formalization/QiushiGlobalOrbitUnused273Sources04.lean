import QiushiGlobalOrbitUnused273Data
import QiushiCertifiedTransport
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane273UnusedGenSource0040 :
    QuotientRankAtLeast (spanCodes [256, 128, 76, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (128, 2), (76, 118), (28, 96), (2, 1), (1, 9)]
    (codeMat 161) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0041 :
    QuotientRankAtLeast (spanCodes [260, 128, 76, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (128, 3), (76, 127), (28, 96), (2, 1), (1, 9)]
    (codeMat 169) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0042 :
    QuotientRankAtLeast (spanCodes [264, 128, 76, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 252), (128, 3), (76, 119), (28, 104), (2, 1), (1, 9)]
    (codeMat 169) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0043 :
    QuotientRankAtLeast (spanCodes [268, 128, 76, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(268, 252), (128, 2), (76, 126), (28, 104), (2, 1), (1, 9)]
    (codeMat 161) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
