import QiushiPlane429GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane429GenSource0020 :
    QuotientRankAtLeast (spanCodes [390, 98, 16, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(390, 384), (98, 85), (16, 32), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0021 :
    QuotientRankAtLeast (spanCodes [288, 172, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 511), (172, 394), (98, 468), (16, 32), (1, 384)]
    (codeMat 159) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0022 :
    QuotientRankAtLeast (spanCodes [290, 174, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(290, 43), (174, 94), (98, 468), (16, 384), (1, 32)]
    (codeMat 143) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0023 :
    QuotientRankAtLeast (spanCodes [294, 168, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(294, 43), (168, 175), (98, 459), (16, 325), (1, 32)]
    (codeMat 335) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 162, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(258, 42), (162, 175), (98, 174), (16, 325), (1, 32)]
    (codeMat 396) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0025 :
    QuotientRankAtLeast (spanCodes [260, 164, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(260, 1), (164, 126), (98, 84), (16, 384), (1, 32)]
    (codeMat 141) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane429GenSource0026 :
    QuotientRankAtLeast (spanCodes [292, 132, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(292, 1), (132, 209), (98, 379), (16, 192), (1, 36)]
    (codeMat 183) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane429GenSource0027 :
    QuotientRankAtLeast (spanCodes [264, 170, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(264, 132), (170, 490), (98, 174), (16, 325), (1, 32)]
    (codeMat 270) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane429GenSource0028 :
    QuotientRankAtLeast (spanCodes [292, 134, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(292, 511), (134, 42), (98, 468), (16, 128), (1, 32)]
    (codeMat 140) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane429GenSource0029 :
    QuotientRankAtLeast (spanCodes [294, 132, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(294, 350), (132, 53), (98, 379), (16, 192), (1, 36)]
    (codeMat 165) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

end QiushiMatmul
