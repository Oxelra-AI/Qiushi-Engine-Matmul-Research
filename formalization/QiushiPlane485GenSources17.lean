import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit31FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0170 :
    QuotientRankAtLeast (spanCodes [260, 132, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(260, 40), (132, 43), (36, 32), (20, 34), (10, 166)]
    (codeMat 214) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0171 :
    QuotientRankAtLeast (spanCodes [256, 128, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 8), (128, 9), (36, 32), (20, 34), (10, 166)]
    (codeMat 212) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0172 :
    QuotientRankAtLeast (spanCodes [320, 198, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(320, 40), (198, 43), (34, 134), (20, 132), (10, 166)]
    (codeMat 158) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0173 :
    QuotientRankAtLeast (spanCodes [325, 195, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(325, 8), (195, 9), (34, 134), (20, 132), (10, 166)]
    (codeMat 157) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0174 :
    QuotientRankAtLeast (spanCodes [288, 128, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(288, 8), (128, 3), (16, 2), (10, 132), (4, 32)]
    (codeMat 86) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0175 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 52), (130, 54), (32, 8), (16, 9), (10, 100), (4, 32)]
    (codeMat 98) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0176 :
    QuotientRankAtLeast (spanCodes [354, 195, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(354, 140), (195, 3), (17, 134), (10, 132), (5, 32)]
    (codeMat 94) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0177 :
    QuotientRankAtLeast (spanCodes [323, 192, 34, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(323, 20), (192, 2), (34, 100), (17, 77), (10, 76), (5, 32)]
    (codeMat 99) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0178 :
    QuotientRankAtLeast (spanCodes [288, 130, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(288, 40), (130, 3), (16, 2), (10, 132), (4, 32)]
    (codeMat 87) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0179 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 20), (128, 2), (32, 8), (16, 1), (10, 68), (4, 32)]
    (codeMat 98) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
