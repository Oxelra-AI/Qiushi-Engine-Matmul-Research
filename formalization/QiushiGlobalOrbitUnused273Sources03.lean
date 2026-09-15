import QiushiGlobalOrbitUnused273Data
import QiushiCertifiedTransport
import QiushiOrbit23FP
import QiushiOrbit31FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane273UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [144, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(144, 216), (80, 88), (8, 8), (4, 4), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane273UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [128, 68, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(128, 32), (68, 68), (20, 80), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane273UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [148, 80, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(148, 118), (80, 22), (32, 128), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [148, 80, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(148, 127), (80, 31), (36, 128), (8, 3), (2, 9), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [148, 80, 48, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(148, 126), (80, 22), (48, 130), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0035 :
    QuotientRankAtLeast (spanCodes [148, 80, 52, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(148, 119), (80, 31), (52, 139), (8, 3), (2, 9), (1, 1)]
    (codeMat 281) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0036 :
    QuotientRankAtLeast (spanCodes [288, 136, 68, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 128), (136, 20), (68, 118), (20, 96), (2, 8), (1, 9)]
    (codeMat 177) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0037 :
    QuotientRankAtLeast (spanCodes [292, 136, 68, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(292, 128), (136, 28), (68, 127), (20, 96), (2, 8), (1, 9)]
    (codeMat 185) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0038 :
    QuotientRankAtLeast (spanCodes [296, 136, 68, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(296, 252), (136, 28), (68, 119), (20, 104), (2, 8), (1, 9)]
    (codeMat 185) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane273UnusedGenSource0039 :
    QuotientRankAtLeast (spanCodes [300, 136, 68, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(300, 252), (136, 20), (68, 126), (20, 104), (2, 8), (1, 9)]
    (codeMat 177) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
