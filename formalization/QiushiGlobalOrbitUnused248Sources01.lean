import QiushiGlobalOrbitUnused248Data
import QiushiCertifiedTransport
import QiushiOrbit23FP
import QiushiOrbit25FP
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane248UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [144, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(144, 216), (80, 88), (8, 8), (4, 4), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane248UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [256, 96, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 128), (96, 80), (8, 8), (4, 2), (2, 4), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane248UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [288, 96, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(288, 216), (96, 88), (8, 8), (4, 3), (2, 4), (1, 1)]
    (codeMat 273) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane248UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [384, 112, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(384, 128), (112, 80), (8, 8), (4, 6), (2, 4), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane248UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [432, 112, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(432, 216), (112, 88), (8, 8), (4, 7), (2, 4), (1, 1)]
    (codeMat 273) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane248UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [368, 144, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(368, 336), (144, 8), (8, 256), (4, 6), (2, 1), (1, 4)]
    (codeMat 177) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane248UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [352, 176, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(352, 264), (176, 336), (8, 256), (4, 5), (2, 2), (1, 4)]
    (codeMat 177) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane248UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [304, 208, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(304, 336), (208, 264), (8, 256), (4, 2), (2, 5), (1, 4)]
    (codeMat 177) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane248UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [288, 240, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(288, 8), (240, 336), (8, 256), (4, 1), (2, 6), (1, 4)]
    (codeMat 177) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane248UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [272, 128, 64, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(272, 160), (128, 16), (64, 8), (8, 64), (4, 4), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
