import QiushiPlane274GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit123From35
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit125From35
import QiushiMonoOrbit129From35T
import QiushiMonoOrbit134From35T
import QiushiMonoOrbit99From35
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane274GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 80, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 20, 8, 2, 1] [(160, 160), (80, 20), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit99_lb15_mono

theorem plane274GenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(160, 160), (80, 80), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane274GenSource0002 :
    QuotientRankAtLeast (spanCodes [160, 64, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(160, 132), (64, 32), (16, 2), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane274GenSource0003 :
    QuotientRankAtLeast (spanCodes [160, 68, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(160, 96), (68, 132), (20, 12), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane274GenSource0004 :
    QuotientRankAtLeast (spanCodes [160, 72, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(160, 166), (72, 32), (24, 2), (2, 9), (1, 8)]
    (codeMat 401) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane274GenSource0005 :
    QuotientRankAtLeast (spanCodes [160, 76, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(160, 232), (76, 134), (28, 14), (2, 3), (1, 2)]
    (codeMat 401) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane274GenSource0006 :
    QuotientRankAtLeast (spanCodes [132, 80, 36, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(132, 12), (80, 81), (36, 256), (2, 1), (1, 2)]
    (codeMat 225) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane274GenSource0007 :
    QuotientRankAtLeast (spanCodes [140, 80, 44, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(140, 95), (80, 81), (44, 258), (2, 3), (1, 2)]
    (codeMat 241) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane274GenSource0008 :
    QuotientRankAtLeast (spanCodes [148, 80, 52, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 132, 12, 2, 1] [(148, 12), (80, 137), (52, 289), (2, 1), (1, 3)]
    (codeMat 313) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit129_lb15_mono

theorem plane274GenSource0009 :
    QuotientRankAtLeast (spanCodes [156, 80, 60, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(156, 156), (80, 82), (60, 35), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

end QiushiMatmul
