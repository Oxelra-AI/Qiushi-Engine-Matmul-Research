import QiushiGlobalOrbitUnused389Data
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane389UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [128, 65, 32, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 216), (65, 128), (32, 63), (17, 11), (9, 2), (5, 40), (3, 8)]
    (codeMat 331) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane389UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 119), (130, 130), (64, 360), (32, 1), (16, 2), (10, 23), (4, 9)]
    (codeMat 474) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane389UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 96), (128, 1), (64, 9), (34, 149), (16, 2), (10, 23), (4, 360)]
    (codeMat 340) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane389UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 257), (130, 8), (65, 9), (33, 490), (17, 21), (10, 23), (5, 360)]
    (codeMat 285) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane389UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [259, 129, 65, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 278), (129, 490), (65, 360), (34, 31), (17, 21), (10, 23), (5, 9)]
    (codeMat 467) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
