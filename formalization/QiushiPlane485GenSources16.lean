import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiStep128Mono158From72
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0160 :
    QuotientRankAtLeast (spanCodes [288, 64, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(288, 16), (64, 192), (19, 350), (10, 245), (7, 36)]
    (codeMat 311) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane485GenSource0161 :
    QuotientRankAtLeast (spanCodes [256, 128, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 8), (128, 1), (16, 2), (10, 132), (4, 32)]
    (codeMat 84) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0162 :
    QuotientRankAtLeast (spanCodes [320, 192, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(320, 8), (192, 1), (17, 134), (10, 132), (5, 32)]
    (codeMat 92) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0163 :
    QuotientRankAtLeast (spanCodes [256, 130, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 40), (130, 1), (16, 2), (10, 132), (4, 32)]
    (codeMat 85) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0164 :
    QuotientRankAtLeast (spanCodes [320, 195, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(320, 40), (195, 1), (17, 134), (10, 132), (5, 32)]
    (codeMat 93) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0165 :
    QuotientRankAtLeast (spanCodes [258, 132, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(258, 20), (132, 52), (38, 43), (20, 53), (10, 222)]
    (codeMat 358) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane485GenSource0166 :
    QuotientRankAtLeast (spanCodes [320, 192, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(320, 8), (192, 9), (34, 134), (20, 132), (10, 166)]
    (codeMat 156) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0167 :
    QuotientRankAtLeast (spanCodes [325, 197, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(325, 40), (197, 43), (34, 134), (20, 132), (10, 166)]
    (codeMat 159) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0168 :
    QuotientRankAtLeast (spanCodes [260, 130, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(260, 8), (130, 9), (36, 32), (20, 34), (10, 166)]
    (codeMat 213) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0169 :
    QuotientRankAtLeast (spanCodes [256, 134, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 40), (134, 43), (36, 32), (20, 34), (10, 166)]
    (codeMat 215) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
