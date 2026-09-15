import QiushiGlobalOrbitUnused291Data
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Mono3032
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane291UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [274, 80, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 104), (80, 252), (32, 9), (10, 31), (4, 1), (1, 3)]
    (codeMat 473) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane291UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [66, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(66, 149), (32, 32), (16, 40), (10, 21), (6, 1), (1, 2)]
    (codeMat 401) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

theorem plane291UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [64, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(64, 128), (32, 32), (18, 63), (10, 23), (6, 3), (1, 2)]
    (codeMat 273) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

end QiushiMatmul
