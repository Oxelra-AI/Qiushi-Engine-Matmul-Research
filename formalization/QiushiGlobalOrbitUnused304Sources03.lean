import QiushiGlobalOrbitUnused304Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit35FP
import QiushiPlane315GenBindings00
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane304UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 16), (164, 170), (68, 10), (16, 260), (10, 69), (1, 1)]
    (codeMat 161) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane304UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [256, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (164, 69), (70, 170), (18, 1), (10, 26), (1, 16)]
    (codeMat 459) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane304UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [256, 166, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (166, 255), (70, 186), (18, 27), (10, 26), (1, 16)]
    (codeMat 394) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane304UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (130, 8), (64, 2), (20, 224), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane304UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 160), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
