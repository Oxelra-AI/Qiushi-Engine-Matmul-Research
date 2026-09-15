import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0080 :
    QuotientRankAtLeast (spanCodes [258, 160, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (160, 252), (64, 3), (10, 148), (6, 130), (1, 2)]
    (codeMat 141) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0081 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 30), (132, 29), (64, 9), (52, 232), (10, 96), (1, 8)]
    (codeMat 205) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0082 :
    QuotientRankAtLeast (spanCodes [258, 164, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 437), (164, 238), (68, 78), (16, 320), (10, 69), (1, 1)]
    (codeMat 177) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane425GenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 166, 68, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 507), (166, 228), (68, 79), (18, 27), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane425GenSource0084 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 81), (144, 1), (80, 33), (50, 91), (10, 100), (1, 365)]
    (codeMat 230) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane425GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 150, 82, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 31), (150, 20), (82, 463), (54, 1), (10, 357), (1, 260)]
    (codeMat 115) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane425GenSource0086 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 22), (132, 20), (64, 9), (54, 128), (10, 104), (1, 8)]
    (codeMat 205) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 284), (128, 32), (82, 296), (32, 63), (10, 265), (1, 365)]
    (codeMat 230) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane425GenSource0088 :
    QuotientRankAtLeast (spanCodes [258, 150, 66, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 227), (150, 28), (66, 97), (38, 224), (10, 104), (1, 8)]
    (codeMat 207) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0089 :
    QuotientRankAtLeast (spanCodes [258, 198, 32, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 278), (198, 371), (32, 32), (20, 52), (10, 42), (1, 63)]
    (codeMat 467) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
